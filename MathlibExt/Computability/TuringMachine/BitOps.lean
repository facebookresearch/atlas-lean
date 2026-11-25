/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Program

/-!
# Bit-string primitives for `TM2` programs

Building blocks for machines that manipulate binary strings stored on stacks, in the style of
`MetaMathlibExt.TM2Program`: each primitive is a statement schema occupying one label, with an
**exact** step count.

A stack `k` holds a *bit block* followed by a rest: a decoder `d : Γ k → Option Bool` reads a
symbol as a bit (`some b`) or as a marker (`none`), and the block is the maximal prefix of bit
symbols. A block ends at the first marker or at the bottom of the stack.

* `moveB a b d g`: pop the bit block of `a` and push it onto `b`, re-encoded by `g` (so it comes
  out reversed); one step per bit plus one (`moveB_run`).
* `cmpB a b da db ea eb`: compare the bit blocks of `a` and `b` without popping a mismatch:
  matching leading bits are moved to the scratch stacks `ta`, `tb`; the run ends at `eqL` if the
  two blocks are equal and at `neL` otherwise, one step per common leading bit plus one
  (`cmpB_run`, which also states that the moved prefix is the longest common one).
* `moveB_restore`: moving a scratch stack back with `moveB` restores the compared stack exactly,
  provided the scratch stack's old contents end a block (empty or a marker on top), the scratch
  decoder reads back what `cmpB` pushed, and the re-encoding gives back the original symbols.

These are the comparison primitives a `TM2` SAT verifier on binary variable names needs (look up
a variable name in a table of names); the state needs only the one bit of `TM2Program.Flag`.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Program

open Turing Function

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- **Bit test for the top of a stack.** Let $d$ be a decoder that reads each symbol either as a
bit or as a marker. For an optional symbol $o$ (the top of a stack, absent when the stack is
empty), the test is true when $o$ is a symbol that $d$ reads as a bit, and false when $o$ is
absent or $d$ reads it as a marker. -/
def isBit {α : Type} (d : α → Option Bool) (o : Option α) : Bool := (o.bind d).isSome

/-- **Bit on top of a stack.** Let $d$ be a decoder that reads each symbol either as a bit or as
a marker. For an optional symbol $o$ (the top of a stack, absent when the stack is empty), the
bit of $o$ under $d$ is $x$ when $o$ is a symbol that $d$ reads as the bit $x$, and false when $o$
is absent or $d$ reads it as a marker. -/
def bitOf {α : Type} (d : α → Option Bool) (o : Option α) : Bool := (o.bind d).getD false

/-- **Bit blocks.** Let $d$ be a decoder that reads each symbol either as a bit or as a marker. A
list of symbols $s_1, \dots, s_n$ is the bit block of a bit string $p$ under $d$ when $p$ has the
same length $n$ and, for each $i$, $d$ reads $s_i$ as the $i$-th bit of $p$. -/
def IsBitBlock {α : Type} (d : α → Option Bool) (xs : List α) (p : List Bool) : Prop :=
  xs.map d = p.map some

/-- **End of a bit block.** Let $d$ be a decoder that reads each symbol either as a bit or as a
marker. A list of symbols $A$ (the rest of a stack below a block) ends a bit block under $d$ when
$A$ is empty or $d$ reads its first symbol as a marker. -/
def EndsBitBlock {α : Type} (d : α → Option Bool) (A : List α) : Prop := A.head?.bind d = none

theorem IsBitBlock.nil_left {α : Type} {d : α → Option Bool} {p : List Bool}
    (h : IsBitBlock d [] p) : p = [] := by
  cases p with
  | nil => rfl
  | cons _ _ => simp [IsBitBlock] at h

theorem IsBitBlock.cons_left {α : Type} {d : α → Option Bool} {x : α} {xs : List α}
    {p : List Bool} (h : IsBitBlock d (x :: xs) p) :
    ∃ b p', p = b :: p' ∧ d x = some b ∧ IsBitBlock d xs p' := by
  cases p with
  | nil => simp [IsBitBlock] at h
  | cons b p' =>
      simp only [IsBitBlock, List.map_cons, List.cons.injEq] at h
      exact ⟨b, p', rfl, h.1, h.2⟩

theorem IsBitBlock.length_eq {α : Type} {d : α → Option Bool} {xs : List α} {p : List Bool}
    (h : IsBitBlock d xs p) : xs.length = p.length := by
  simpa using congrArg List.length h

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

/-! ### Moving a bit block -/

section Move

/-- **Bit-moving loop.** For stacks $a$ and $b$, a decoder $d$ reading each symbol of $a$ as a bit
or a marker, an encoder $g$ from bits to symbols of $b$, and labels $\mathit{self}$ and
$\mathit{next}$, the bit-moving loop from $a$ to $b$ is the statement that looks at the top of
$a$: if it is a symbol that $d$ reads as a bit $x$, it pops it, pushes $g(x)$ onto $b$ and goes to
$\mathit{self}$; if it is a marker or $a$ is empty, it goes to $\mathit{next}$. It overwrites the
state with a flag bit, used as scratch. -/
def moveB (a b : K) (d : Γ a → Option Bool) (g : Bool → Γ b) (self next : Λ) :
    TM2.Stmt Γ Λ σ :=
  .peek a (fun _ o => Flag.tag (isBit d o))
    (.branch Flag.untag
      (.pop a (fun _ o => Flag.tag (bitOf d o))
        (.branch Flag.untag
          (.push b (fun _ => g true) (.goto fun _ => self))
          (.push b (fun _ => g false) (.goto fun _ => self))))
      (.goto fun _ => next))

/-- **Running the bit-moving loop.** Let $a \ne b$ be stacks of a program $M$ whose state carries
a flag bit, $d$ a decoder reading each symbol of $a$ as a bit or a marker, $g$ an encoder from bits
to symbols of $b$, and $\mathit{self}$, $\mathit{next}$ labels such that $M$ runs at
$\mathit{self}$ the bit-moving loop from $a$ to $b$ with decoder $d$ and encoder $g$, looping at
$\mathit{self}$ and exiting to $\mathit{next}$. Let $p = p_1 \cdots p_n$ be a bit list and $S$
stack contents in which $a$ holds a bit block for $p$ under $d$ followed by a rest $A$ that ends a
bit block under $d$. Then for every state $v$ there are a state $v'$ and stack contents $S'$ such
that $M$ runs in exactly $n + 1$ steps from label $\mathit{self}$, state $v$ and stacks $S$ to
label $\mathit{next}$, state $v'$ and stacks $S'$, where $S'(a) = A$, $S'(b)$ is
$g(p_n), \dots, g(p_1)$ (top first) followed by $S(b)$, and $S'(k) = S(k)$ for every other stack
$k$. -/
theorem moveB_run {self next : Λ} {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    (hp : M self = moveB a b d g self next) (hab : a ≠ b) :
    ∀ (p : List Bool) (xs A : List (Γ a)) (v : σ) (S : ∀ k, List (Γ k)),
      S a = xs ++ A → IsBitBlock d xs p → EndsBitBlock d A →
      ∃ v' S', Run M (p.length + 1) ⟨some self, v, S⟩ ⟨some next, v', S'⟩ ∧
        S' a = A ∧ S' b = (p.map g).reverse ++ S b ∧ ∀ k, k ≠ a → k ≠ b → S' k = S k := by
  intro p
  induction p with
  | nil =>
      intro xs A v S hS hxs hA
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hxs.length_eq)
      subst hx
      refine ⟨Flag.tag false, S, Run.single ?_, by simpa using hS, by simp, fun _ _ _ => rfl⟩
      have h2 : isBit d (S a).head? = false := by
        simp only [isBit, hS, List.nil_append]
        simpa [EndsBitBlock] using hA
      simp only [hp, moveB, TM2.stepAux, h2, Flag.untag_tag, Bool.cond_false]
  | cons bit p ih =>
      intro xs A v S hS hxs hA
      cases xs with
      | nil => exact absurd hxs.nil_left (by simp)
      | cons x xs =>
          obtain ⟨b', p', hpe, hdx, hxs'⟩ := hxs.cons_left
          obtain ⟨rfl, rfl⟩ := List.cons.inj hpe
          set S₁ := update (update S a (xs ++ A)) b (g bit :: S b) with hS₁
          have h₁ : S₁ a = xs ++ A := by
            rw [hS₁, update_of_ne hab, update_self]
          obtain ⟨v', S', hrun, ha', hb', hk'⟩ := ih xs A (Flag.tag bit) S₁ h₁ hxs' hA
          have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag bit, S₁⟩ := by
            have hh : (S a).head? = some x := by simp [hS]
            have hb : isBit d (some x) = true := by simp [isBit, hdx]
            have hv : bitOf d (some x) = bit := by simp [bitOf, hdx]
            have ht : (S a).tail = xs ++ A := by simp [hS]
            cases bit <;>
              simp [TM2.step, hp, moveB, TM2.stepAux, hh, hb, hv, ht, hS₁, update_of_ne hab.symm]
          refine ⟨v', S', Run.head hstep hrun, ha', ?_, fun k hka hkb => ?_⟩
          · rw [hb', hS₁, update_self]; simp
          · rw [hk' k hka hkb, hS₁, update_of_ne hkb, update_of_ne hka]

end Move

/-! ### Comparing two bit blocks -/

section Compare

/-- **Bit-block comparison statement.** Let $a$ and $b$ be stacks with decoders $d_a$ and $d_b$
that read each symbol either as a bit or as a marker, let $t_a$ and $t_b$ be scratch stacks with
bit encoders $e_a$ and $e_b$, and let $\ell$, $\ell_=$ and $\ell_{\ne}$ be labels. The comparison
statement with loop label $\ell$ performs one round of comparison: if the tops of $a$ and $b$ are
the same bit $x$, it pops both, pushes $e_a(x)$ onto $t_a$ and $e_b(x)$ onto $t_b$, and goes to
$\ell$. Otherwise it changes no stack: it goes to $\ell_=$ if neither top is a bit (each of $a$
and $b$ is empty or has a marker on top), and to $\ell_{\ne}$ if the tops are different bits or
exactly one of them is a bit. It records its tests in the one-bit flag of the machine state. -/
def cmpB (a b ta tb : K) (da : Γ a → Option Bool) (db : Γ b → Option Bool)
    (ea : Bool → Γ ta) (eb : Bool → Γ tb) (self eqL neL : Λ) : TM2.Stmt Γ Λ σ :=
  .peek a (fun _ o => Flag.tag (isBit da o))
    (.branch Flag.untag
      (.peek a (fun _ o => Flag.tag (bitOf da o))
        (.branch Flag.untag
          (.peek b (fun _ o => Flag.tag (decide (o.bind db = some true)))
            (.branch Flag.untag
              (.pop a (fun s _ => s) (.pop b (fun s _ => s)
                (.push ta (fun _ => ea true) (.push tb (fun _ => eb true)
                  (.goto fun _ => self)))))
              (.goto fun _ => neL)))
          (.peek b (fun _ o => Flag.tag (decide (o.bind db = some false)))
            (.branch Flag.untag
              (.pop a (fun s _ => s) (.pop b (fun s _ => s)
                (.push ta (fun _ => ea false) (.push tb (fun _ => eb false)
                  (.goto fun _ => self)))))
              (.goto fun _ => neL)))))
      (.peek b (fun _ o => Flag.tag (isBit db o))
        (.branch Flag.untag (.goto fun _ => neL) (.goto fun _ => eqL))))

variable {a b ta tb : K} {da : Γ a → Option Bool} {db : Γ b → Option Bool}
  {ea : Bool → Γ ta} {eb : Bool → Γ tb} {self eqL neL : Λ}

/-- **Four pairwise distinct stacks.** Four stack indices $a$, $b$, $t_a$, $t_b$ are pairwise
distinct: $a \ne b$, $a \ne t_a$, $a \ne t_b$, $b \ne t_a$, $b \ne t_b$ and $t_a \ne t_b$.

These are the two compared stacks and the two scratch stacks of the bit-block comparison. -/
structure Distinct4 (a b ta tb : K) : Prop where
  /-- The compared stacks differ. -/
  ab : a ≠ b
  /-- `a` is not the first scratch stack. -/
  ata : a ≠ ta
  /-- `a` is not the second scratch stack. -/
  atb : a ≠ tb
  /-- `b` is not the first scratch stack. -/
  bta : b ≠ ta
  /-- `b` is not the second scratch stack. -/
  btb : b ≠ tb
  /-- The scratch stacks differ. -/
  tatb : ta ≠ tb

/-- **Comparison pops a common prefix.** Suppose the program has at label $\ell$ the bit-block
comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$) with scratch stacks $t_a$ and
$t_b$ (encoders $e_a$, $e_b$) and loop label $\ell$, and that $a$, $b$, $t_a$, $t_b$ are pairwise
distinct. Let $p = p_1 \dots p_n$ be a bit string, and take a configuration at label $\ell$, with
any state, in which stack $a$ holds a list $X$ on top of $A$ and stack $b$ holds a list $Y$ on
top of $B$, where $X$ is the bit block $p$ under $d_a$ and $Y$ is the bit block $p$ under $d_b$.
Then in exactly $n$ steps the program reaches a configuration at label $\ell$, with some state,
in which stack $a$ is $A$, stack $b$ is $B$, stack $t_a$ holds $e_a(p_n), \dots, e_a(p_1)$ on top
of its old contents, stack $t_b$ holds $e_b(p_n), \dots, e_b(p_1)$ on top of its old contents,
and every other stack is unchanged. -/
theorem cmpB_prefix (hp : M self = cmpB a b ta tb da db ea eb self eqL neL)
    (hd : Distinct4 a b ta tb) :
    ∀ (p : List Bool) (xs A : List (Γ a)) (ys B : List (Γ b)) (v : σ) (S : ∀ k, List (Γ k)),
      S a = xs ++ A → S b = ys ++ B → IsBitBlock da xs p → IsBitBlock db ys p →
      ∃ v' S', Run M p.length ⟨some self, v, S⟩ ⟨some self, v', S'⟩ ∧
        S' a = A ∧ S' b = B ∧ S' ta = (p.map ea).reverse ++ S ta ∧
        S' tb = (p.map eb).reverse ++ S tb ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ ta → k ≠ tb → S' k = S k := by
  intro p
  induction p with
  | nil =>
      intro xs A ys B v S hSa hSb hxs hys
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hxs.length_eq)
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hys.length_eq)
      subst hx hy
      exact ⟨v, S, Run.zero _, by simpa using hSa, by simpa using hSb, by simp, by simp,
        fun _ _ _ _ _ => rfl⟩
  | cons bit p ih =>
      intro xs A ys B v S hSa hSb hxs hys
      cases xs with
      | nil => exact absurd hxs.nil_left (by simp)
      | cons x xs =>
      cases ys with
      | nil => exact absurd hys.nil_left (by simp)
      | cons y ys =>
          obtain ⟨b₁, p₁, hp₁, hdx, hxs'⟩ := hxs.cons_left
          obtain ⟨b₂, p₂, hp₂, hdy, hys'⟩ := hys.cons_left
          obtain ⟨rfl, rfl⟩ := List.cons.inj hp₁
          obtain ⟨rfl, rfl⟩ := List.cons.inj hp₂
          set S₁ := update (update (update (update S a (xs ++ A)) b (ys ++ B)) ta
            (ea bit :: S ta)) tb (eb bit :: S tb) with hS₁
          have h₁a : S₁ a = xs ++ A := by
            simp [hS₁, update_of_ne hd.atb, update_of_ne hd.ata, update_of_ne hd.ab]
          have h₁b : S₁ b = ys ++ B := by
            simp [hS₁, update_of_ne hd.btb, update_of_ne hd.bta]
          obtain ⟨v', S', hrun, ha', hb', hta', htb', hk'⟩ :=
            ih xs A ys B (Flag.tag true) S₁ h₁a h₁b hxs' hys'
          have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
            have hha : (S a).head? = some x := by simp [hSa]
            have hhb : (S b).head? = some y := by simp [hSb]
            have hta : (S a).tail = xs ++ A := by simp [hSa]
            have htb : (S b).tail = ys ++ B := by simp [hSb]
            have hb : isBit da (some x) = true := by simp [isBit, hdx]
            have hv : bitOf da (some x) = bit := by simp [bitOf, hdx]
            cases bit <;>
              simp [TM2.step, hp, cmpB, TM2.stepAux, hha, hhb, hta, htb, hb, hv, hdy, hS₁,
                update_of_ne hd.ab.symm, update_of_ne hd.bta.symm, update_of_ne hd.btb.symm,
                update_of_ne hd.tatb.symm, update_of_ne hd.ata.symm, update_of_ne hd.atb.symm]
          refine ⟨v', S', Run.head hstep hrun, ha', hb', ?_, ?_, fun k h1 h2 h3 h4 => ?_⟩
          · rw [hta', hS₁, update_of_ne hd.tatb, update_self]; simp
          · rw [htb', hS₁, update_self]; simp
          · rw [hk' k h1 h2 h3 h4, hS₁, update_of_ne h4, update_of_ne h3, update_of_ne h2,
              update_of_ne h1]

/-- **Deciding step of the comparison.** Suppose the program has at label $\ell$ the bit-block
comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$; scratch stacks arbitrary) with
loop label $\ell$, equality label $\ell_=$ and mismatch label $\ell_{\ne}$. From a configuration
at label $\ell$, with any state, in which the tops of $a$ and $b$ are not the same bit, the
program takes one step to a configuration with the same stacks and some state, at label $\ell_=$
if neither top is a bit (each of $a$ and $b$ is empty or has a marker on top) and at label
$\ell_{\ne}$ otherwise. -/
theorem cmpB_last (hp : M self = cmpB a b ta tb da db ea eb self eqL neL) (v : σ)
    (S : ∀ k, List (Γ k))
    (h : ¬ ∃ c, (S a).head?.bind da = some c ∧ (S b).head?.bind db = some c) :
    ∃ v', Run M 1 ⟨some self, v, S⟩
      ⟨some (if (S a).head?.bind da = none ∧ (S b).head?.bind db = none then eqL else neL),
        v', S⟩ := by
  cases ha : (S a).head?.bind da with
  | none =>
      cases hb : (S b).head?.bind db with
      | none =>
          refine ⟨Flag.tag false, Run.single ?_⟩
          simp [cmpB, hp, TM2.stepAux, isBit, ha, hb]
      | some c =>
          refine ⟨Flag.tag true, Run.single ?_⟩
          simp [cmpB, hp, TM2.stepAux, isBit, ha, hb]
  | some c =>
      have hb : (S b).head?.bind db ≠ some c := fun hb => h ⟨c, ha, hb⟩
      refine ⟨Flag.tag false, Run.single ?_⟩
      cases c <;> simp [cmpB, hp, TM2.stepAux, isBit, bitOf, ha, hb]

/-- **Correctness of the bit-block comparison.** Suppose the program has at label $\ell$ the
bit-block comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$) with scratch stacks
$t_a$ and $t_b$ (encoders $e_a$, $e_b$), loop label $\ell$, equality label $\ell_=$ and mismatch
label $\ell_{\ne}$, and that $a$, $b$, $t_a$, $t_b$ are pairwise distinct. Let $u$ and $w$ be bit
strings, and take a configuration at label $\ell$, with any state, in which stack $a$ holds a
list $X$ on top of $A$ and stack $b$ holds a list $Y$ on top of $B$, where $X$ is the bit block
$u$ under $d_a$, $Y$ is the bit block $w$ under $d_b$, $A$ ends a bit block under $d_a$ and $B$
ends a bit block under $d_b$. Then there is a common prefix $c = c_1 \dots c_m$ of $u$ and $w$,
after which $u$ and $w$ do not continue with the same bit, such that in exactly $m + 1$ steps the
program reaches a configuration, with some state, at label $\ell_=$ if $u = w$ and at label
$\ell_{\ne}$ otherwise, in which stack $a$ holds $X$ without its first $m$ symbols on top of $A$,
stack $b$ holds $Y$ without its first $m$ symbols on top of $B$, stack $t_a$ holds
$e_a(c_m), \dots, e_a(c_1)$ on top of its old contents, stack $t_b$ holds
$e_b(c_m), \dots, e_b(c_1)$ on top of its old contents, and every other stack is unchanged. -/
theorem cmpB_run (hp : M self = cmpB a b ta tb da db ea eb self eqL neL)
    (hd : Distinct4 a b ta tb) :
    ∀ (u w : List Bool) (xs A : List (Γ a)) (ys B : List (Γ b)) (v : σ) (S : ∀ k, List (Γ k)),
      S a = xs ++ A → S b = ys ++ B → IsBitBlock da xs u → IsBitBlock db ys w → EndsBitBlock da A →
      EndsBitBlock db B →
      ∃ (c : List Bool) (v' : σ) (S' : ∀ k, List (Γ k)), c <+: u ∧ c <+: w ∧
        (∀ bit, (u.drop c.length).head? = some bit → (w.drop c.length).head? ≠ some bit) ∧
        Run M (c.length + 1) ⟨some self, v, S⟩ ⟨some (if u = w then eqL else neL), v', S'⟩ ∧
        S' a = xs.drop c.length ++ A ∧ S' b = ys.drop c.length ++ B ∧
        S' ta = (c.map ea).reverse ++ S ta ∧ S' tb = (c.map eb).reverse ++ S tb ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ ta → k ≠ tb → S' k = S k := by
  intro u
  induction u with
  | nil =>
      intro w xs A ys B v S hSa hSb hxs hys hA hB
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hxs.length_eq)
      subst hx
      have ha : (S a).head?.bind da = none := by rw [hSa, List.nil_append]; exact hA
      cases w with
      | nil =>
          have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hys.length_eq)
          subst hy
          have hb : (S b).head?.bind db = none := by rw [hSb, List.nil_append]; exact hB
          obtain ⟨v', hrun⟩ := cmpB_last hp v S (by simp [ha])
          refine ⟨[], v', S, List.nil_prefix, List.nil_prefix, by simp, ?_, by simpa using hSa,
            by simpa using hSb, by simp, by simp, fun _ _ _ _ _ => rfl⟩
          simpa [ha, hb] using hrun
      | cons b₂ w =>
          obtain ⟨y, ys', rfl, -⟩ : ∃ y ys', ys = y :: ys' ∧ True := by
            cases ys with
            | nil => exact absurd hys.nil_left (by simp)
            | cons y ys' => exact ⟨y, ys', rfl, trivial⟩
          obtain ⟨_, _, hpe, hdy, _⟩ := hys.cons_left
          obtain ⟨rfl, rfl⟩ := List.cons.inj hpe
          obtain ⟨v', hrun⟩ := cmpB_last hp v S (by simp [ha])
          refine ⟨[], v', S, List.nil_prefix, List.nil_prefix, by simp, ?_, by simpa using hSa,
            by simp [hSb], by simp, by simp, fun _ _ _ _ _ => rfl⟩
          simpa [ha, hSb, hdy] using hrun
  | cons b₁ u ih =>
      intro w xs A ys B v S hSa hSb hxs hys hA hB
      cases xs with
      | nil => exact absurd hxs.nil_left (by simp)
      | cons x xs =>
      obtain ⟨_, _, hpe, hdx, hxs'⟩ := hxs.cons_left
      obtain ⟨rfl, rfl⟩ := List.cons.inj hpe
      have ha : (S a).head?.bind da = some b₁ := by simp [hSa, hdx]
      cases w with
      | nil =>
          have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hys.length_eq)
          subst hy
          have hb : (S b).head?.bind db = none := by rw [hSb, List.nil_append]; exact hB
          obtain ⟨v', hrun⟩ := cmpB_last hp v S (by simp [ha, hb])
          refine ⟨[], v', S, List.nil_prefix, List.nil_prefix, by simp, ?_, by simp [hSa],
            by simpa using hSb, by simp, by simp, fun _ _ _ _ _ => rfl⟩
          simpa [ha, hb] using hrun
      | cons b₂ w =>
          cases ys with
          | nil => exact absurd hys.nil_left (by simp)
          | cons y ys =>
          obtain ⟨_, _, hpe₂, hdy, hys'⟩ := hys.cons_left
          obtain ⟨rfl, rfl⟩ := List.cons.inj hpe₂
          have hb : (S b).head?.bind db = some b₂ := by simp [hSb, hdy]
          by_cases h12 : b₁ = b₂
          · subst h12
            obtain ⟨v₁, S₁, hrun₁, h1a, h1b, h1ta, h1tb, h1k⟩ :=
              cmpB_prefix hp hd [b₁] [x] (xs ++ A) [y] (ys ++ B) v S (by simp [hSa])
                (by simp [hSb]) (by simp [IsBitBlock, hdx]) (by simp [IsBitBlock, hdy])
            obtain ⟨c, v', S', hcu, hcw, hmax, hrun, h2a, h2b, h2ta, h2tb, h2k⟩ :=
              ih w xs A ys B v₁ S₁ h1a h1b hxs' hys' hA hB
            refine ⟨b₁ :: c, v', S', List.cons_prefix_cons.2 ⟨rfl, hcu⟩,
              List.cons_prefix_cons.2 ⟨rfl, hcw⟩, by simpa using hmax, ?_, by simpa using h2a,
              by simpa using h2b, ?_, ?_,
              fun k k1 k2 k3 k4 => by rw [h2k k k1 k2 k3 k4, h1k k k1 k2 k3 k4]⟩
            · have h := hrun₁.trans hrun
              simp only [List.cons.injEq, true_and]
              exact h.of_eq (by simp only [List.length_cons, List.length_nil]; omega)
            · rw [h2ta, h1ta]; simp
            · rw [h2tb, h1tb]; simp
          · obtain ⟨v', hrun⟩ := cmpB_last hp v S (by
              rintro ⟨c, hc1, hc2⟩
              rw [ha] at hc1; rw [hb] at hc2
              exact h12 ((Option.some.inj hc1).trans (Option.some.inj hc2).symm))
            refine ⟨[], v', S, List.nil_prefix, List.nil_prefix, by simpa [eq_comm] using h12, ?_,
              by simp [hSa], by simp [hSb], by simp, by simp, fun _ _ _ _ _ => rfl⟩
            simpa [ha, hb, h12] using hrun

/-- **Recovering a bit block from its bits.** Let $d$ be a decoder reading symbols as bits or
markers and $g$ an encoder from bits to symbols such that $g(b) = x$ whenever $d$ reads $x$ as the
bit $b$. If the symbol list $xs$ is a bit block for the bit list $u$ under $d$ and
$c = c_1 \cdots c_m$ is a prefix of $u$, then the first $m$ symbols of $xs$ are
$g(c_1), \dots, g(c_m)$. -/
theorem IsBitBlock.take_eq_map {α : Type} {d : α → Option Bool} {g : Bool → α}
    (hg : ∀ x b, d x = some b → g b = x) :
    ∀ {xs : List α} {u c : List Bool}, IsBitBlock d xs u → c <+: u → xs.take c.length = c.map g
  | xs, u, [], _, _ => by simp
  | [], _, _ :: _, hxs, hc => by
      rw [hxs.nil_left] at hc
      exact absurd hc (by simp)
  | x :: xs, u, b :: c, hxs, hc => by
      obtain ⟨b', u', rfl, hdx, hxs'⟩ := hxs.cons_left
      obtain ⟨rfl, hc'⟩ := List.cons_prefix_cons.1 hc
      simp [hg x b hdx, IsBitBlock.take_eq_map hg hxs' hc']

/-- **Restoring a stack after a comparison.** Let $t \ne a$ be stacks with decoders $d_t$ and
$d_a$ that read each symbol either as a bit or as a marker. Let $e_t$ be a bit encoder for $t$
that $d_t$ reads back ($d_t$ reads $e_t(x)$ as the bit $x$), and let $g_a$ be a bit encoder for
$a$ that inverts $d_a$ ($g_a(x) = s$ whenever $d_a$ reads the symbol $s$ as the bit $x$). Suppose
the program has at label $\ell$ the bit-block move statement from $t$ (decoder $d_t$) onto $a$
(re-encoding $g_a$) with loop label $\ell$ and exit label $\ell'$. Let $X$ be the bit block of a
bit string $u$ under $d_a$ and let $c = c_1 \dots c_m$ be a prefix of $u$. From a configuration
at label $\ell$, with any state, in which stack $t$ holds $e_t(c_m), \dots, e_t(c_1)$ on top of a
list $R$ that ends a bit block under $d_t$, and stack $a$ holds $X$ without its first $m$ symbols
on top of a list $A$, the program reaches in exactly $m + 1$ steps a configuration at label
$\ell'$, with some state, in which stack $t$ is $R$, stack $a$ holds $X$ on top of $A$, and every
other stack is unchanged. -/
theorem moveB_restore {t : K} {dt : Γ t → Option Bool} {et : Bool → Γ t} {ga : Bool → Γ a}
    {self' next : Λ} (hp : M self' = moveB t a dt ga self' next) (hta : t ≠ a)
    (hdt : ∀ bit, dt (et bit) = some bit) (hga : ∀ x bit, da x = some bit → ga bit = x)
    (u c : List Bool) (xs A : List (Γ a)) (R : List (Γ t)) (v : σ) (S : ∀ k, List (Γ k))
    (hxs : IsBitBlock da xs u) (hc : c <+: u) (hSt : S t = (c.map et).reverse ++ R)
    (hSa : S a = xs.drop c.length ++ A) (hR : EndsBitBlock dt R) :
    ∃ v' S', Run M (c.length + 1) ⟨some self', v, S⟩ ⟨some next, v', S'⟩ ∧
      S' t = R ∧ S' a = xs ++ A ∧ ∀ k, k ≠ t → k ≠ a → S' k = S k := by
  have hblk : IsBitBlock dt (c.map et).reverse c.reverse := by
    simp [IsBitBlock, List.map_reverse, hdt]
  obtain ⟨v', S', hrun, ht, ha, hk⟩ := moveB_run hp hta c.reverse _ R v S hSt hblk hR
  refine ⟨v', S', by simpa using hrun, ht, ?_, hk⟩
  rw [ha, hSa, List.map_reverse, List.reverse_reverse, ← hxs.take_eq_map hga hc,
    ← List.append_assoc, List.take_append_drop]

end Compare

end MetaMathlibExt.TM2Program
