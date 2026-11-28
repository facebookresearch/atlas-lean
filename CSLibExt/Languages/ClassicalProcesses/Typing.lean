/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Foundations.Logic.InferenceSystem.Defs
public import Cslib.Logics.LinearLogic.CLL.Basic
public import CSLibExt.Languages.PiCalculus.Basic
public import Mathlib.Data.Finmap
public import Mathlib.Data.Finset.Basic

/-!
# Classical processes: typing

The exponential- and quantifier-free fragment of Wadler's classical
processes from *Propositions as Sessions* (ICFP 2012), Figure 1.
A process is typed by a finite map from channel names to propositions of
classical linear logic. Erasing the names from such a context gives a
one-sided CLL sequent, and every typing derivation erases to a CLL
derivation of that sequent. The development also records invariance under
injective channel renaming, the substitution used by the axiom-cut rule,
and that every syntactically free channel of a typed process occurs in its
context.

Channel names use the existing π-calculus convention: `Name.const n` is a
free channel and `Name.var i` refers to the `i`-th enclosing binder.
Cut binds `var 0` in both components; bound output binds `var 0` only in
its first component; input binds `var 0` in its continuation.

No reduction, structural equivalence, preservation, deadlock freedom,
exponentials, quantifiers, or GV translation is formalized here.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.ClassicalProcesses

variable {Atom : Type u}

/-- A CP environment: a finite map from channel names to CLL
propositions. The order of entries is ignored, as in the source. -/
abbrev Context (Atom : Type u) : Type u :=
  Finmap (fun _ : PiCalculus.Name => Logic.CLL.Proposition Atom)

/-- Map the keys of a CP environment along an injective renaming of
channel names, preserving the associated propositions and their order in
the underlying entries. -/
def Context.mapKeys (f : PiCalculus.Name → PiCalculus.Name)
    (hf : Function.Injective f) (Γ : Context Atom) : Context Atom where
  entries := Γ.entries.map (fun e => ⟨f e.1, e.2⟩)
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    have h := Γ.nodupKeys.nodup_keys
    simpa [Multiset.keys, Multiset.map_map] using h.map hf

/-- Push a CP environment under one additional binder. Free constants are
unchanged and every de Bruijn variable is shifted up by one. -/
def Context.lift (Γ : Context Atom) : Context Atom :=
  Γ.mapKeys (PiCalculus.liftName 0) (by
    intro a b h
    cases a <;> cases b <;> simp_all [PiCalculus.liftName])

/-- Erase channel names from a CP environment, returning the multiset of
propositions in the corresponding one-sided CLL sequent. -/
def Context.eraseNames (Γ : Context Atom) : Logic.CLL.Sequent Atom :=
  Γ.entries.map Sigma.snd

/-- Processes in the exponential- and quantifier-free fragment of CP.
Cut annotations range over all CLL propositions, as in the source, even
though no process rule in this fragment introduces an exponential. -/
inductive Proc (Atom : Type u) where
  | link (x y : PiCalculus.Name) : Proc Atom
  | cut (a : Logic.CLL.Proposition Atom) (p q : Proc Atom) : Proc Atom
  | output (x : PiCalculus.Name) (p q : Proc Atom) : Proc Atom
  | input (x : PiCalculus.Name) (p : Proc Atom) : Proc Atom
  | selectLeft (x : PiCalculus.Name) (p : Proc Atom) : Proc Atom
  | selectRight (x : PiCalculus.Name) (p : Proc Atom) : Proc Atom
  | choice (x : PiCalculus.Name) (p q : Proc Atom) : Proc Atom
  | emptyOutput (x : PiCalculus.Name) : Proc Atom
  | emptyInput (x : PiCalculus.Name) (p : Proc Atom) : Proc Atom
  | emptyChoice (x : PiCalculus.Name) : Proc Atom

/-- Shift de Bruijn variables at or above `cutoff`, in the same way as
for π-calculus processes. -/
def Proc.liftAt (cutoff : ℕ) : Proc Atom → Proc Atom
  | .link x y =>
      .link (PiCalculus.liftName cutoff x) (PiCalculus.liftName cutoff y)
  | .cut a p q =>
      .cut a (Proc.liftAt (cutoff + 1) p) (Proc.liftAt (cutoff + 1) q)
  | .output x p q =>
      .output (PiCalculus.liftName cutoff x)
        (Proc.liftAt (cutoff + 1) p) (Proc.liftAt cutoff q)
  | .input x p =>
      .input (PiCalculus.liftName cutoff x) (Proc.liftAt (cutoff + 1) p)
  | .selectLeft x p =>
      .selectLeft (PiCalculus.liftName cutoff x) (Proc.liftAt cutoff p)
  | .selectRight x p =>
      .selectRight (PiCalculus.liftName cutoff x) (Proc.liftAt cutoff p)
  | .choice x p q =>
      .choice (PiCalculus.liftName cutoff x)
        (Proc.liftAt cutoff p) (Proc.liftAt cutoff q)
  | .emptyOutput x => .emptyOutput (PiCalculus.liftName cutoff x)
  | .emptyInput x p =>
      .emptyInput (PiCalculus.liftName cutoff x) (Proc.liftAt cutoff p)
  | .emptyChoice x => .emptyChoice (PiCalculus.liftName cutoff x)

/-- Substitute a channel name for the de Bruijn variable at `cutoff`,
lowering higher variables and lifting the replacement under binders so
that it is not captured. -/
def Proc.substAt (n : PiCalculus.Name) (cutoff : ℕ) :
    Proc Atom → Proc Atom
  | .link x y =>
      .link (PiCalculus.substName n cutoff x)
        (PiCalculus.substName n cutoff y)
  | .cut a p q =>
      .cut a (Proc.substAt (PiCalculus.liftName 0 n) (cutoff + 1) p)
        (Proc.substAt (PiCalculus.liftName 0 n) (cutoff + 1) q)
  | .output x p q =>
      .output (PiCalculus.substName n cutoff x)
        (Proc.substAt (PiCalculus.liftName 0 n) (cutoff + 1) p)
        (Proc.substAt n cutoff q)
  | .input x p =>
      .input (PiCalculus.substName n cutoff x)
        (Proc.substAt (PiCalculus.liftName 0 n) (cutoff + 1) p)
  | .selectLeft x p =>
      .selectLeft (PiCalculus.substName n cutoff x)
        (Proc.substAt n cutoff p)
  | .selectRight x p =>
      .selectRight (PiCalculus.substName n cutoff x)
        (Proc.substAt n cutoff p)
  | .choice x p q =>
      .choice (PiCalculus.substName n cutoff x)
        (Proc.substAt n cutoff p) (Proc.substAt n cutoff q)
  | .emptyOutput x => .emptyOutput (PiCalculus.substName n cutoff x)
  | .emptyInput x p =>
      .emptyInput (PiCalculus.substName n cutoff x)
        (Proc.substAt n cutoff p)
  | .emptyChoice x => .emptyChoice (PiCalculus.substName n cutoff x)

/-- Substitute a channel name for the innermost bound variable. This is
the substitution appearing in the source's axiom-cut reduction. -/
def Proc.subst (p : Proc Atom) (n : PiCalculus.Name) : Proc Atom :=
  Proc.substAt n 0 p

/-- Lift a channel renaming under one binder: the newly bound variable is
fixed, and every name produced by the original renaming is shifted so
that it still refers to the same outer channel. -/
def liftRename (f : PiCalculus.Name → PiCalculus.Name) :
    PiCalculus.Name → PiCalculus.Name
  | .const n => PiCalculus.liftName 0 (f (.const n))
  | .var 0 => .var 0
  | .var (i + 1) => PiCalculus.liftName 0 (f (.var i))

/-- Apply a renaming to every free channel name in a process, respecting
the three binders in the CP grammar. -/
def Proc.rename (f : PiCalculus.Name → PiCalculus.Name) :
    Proc Atom → Proc Atom
  | .link x y => .link (f x) (f y)
  | .cut a p q =>
      .cut a (Proc.rename (liftRename f) p) (Proc.rename (liftRename f) q)
  | .output x p q =>
      .output (f x) (Proc.rename (liftRename f) p) (Proc.rename f q)
  | .input x p => .input (f x) (Proc.rename (liftRename f) p)
  | .selectLeft x p => .selectLeft (f x) (Proc.rename f p)
  | .selectRight x p => .selectRight (f x) (Proc.rename f p)
  | .choice x p q => .choice (f x) (Proc.rename f p) (Proc.rename f q)
  | .emptyOutput x => .emptyOutput (f x)
  | .emptyInput x p => .emptyInput (f x) (Proc.rename f p)
  | .emptyChoice x => .emptyChoice (f x)

/-- The free names contributed by one name occurrence under `depth`
binders. A variable below the depth is bound; a variable at or above the
depth is reported in the coordinates of the ambient process. -/
def freeNameAt (depth : ℕ) (x : PiCalculus.Name) :
    Finset PiCalculus.Name :=
  match x with
  | .const n => {(.const n : PiCalculus.Name)}
  | .var i => if i < depth then ∅ else {(.var (i - depth) : PiCalculus.Name)}

/-- The free channel names of a process under `depth` enclosing binders,
reported in ambient coordinates. -/
def Proc.freeNamesAt (depth : ℕ) : Proc Atom → Finset PiCalculus.Name
  | .link x y => freeNameAt depth x ∪ freeNameAt depth y
  | .cut _ p q =>
      Proc.freeNamesAt (depth + 1) p ∪ Proc.freeNamesAt (depth + 1) q
  | .output x p q =>
      freeNameAt depth x ∪ Proc.freeNamesAt (depth + 1) p ∪
        Proc.freeNamesAt depth q
  | .input x p => freeNameAt depth x ∪ Proc.freeNamesAt (depth + 1) p
  | .selectLeft x p => freeNameAt depth x ∪ Proc.freeNamesAt depth p
  | .selectRight x p => freeNameAt depth x ∪ Proc.freeNamesAt depth p
  | .choice x p q =>
      freeNameAt depth x ∪ Proc.freeNamesAt depth p ∪
        Proc.freeNamesAt depth q
  | .emptyOutput x => freeNameAt depth x
  | .emptyInput x p => freeNameAt depth x ∪ Proc.freeNamesAt depth p
  | .emptyChoice x => freeNameAt depth x

/-- The free channel names of a process. -/
def Proc.freeNames (p : Proc Atom) : Finset PiCalculus.Name :=
  Proc.freeNamesAt 0 p

/-- The CP typing judgment from Figure 1, restricted to the fragment
without exponentials and quantifiers. In each rule, the displayed
environment is built by disjoint extension or union; the side conditions
make the source's implicit distinctness requirements explicit. There is
intentionally no rule for `0`. -/
inductive HasType : Context Atom → Proc Atom → Prop where
  | ax {w x : PiCalculus.Name} {a : Logic.CLL.Proposition Atom}
      (hwx : w ≠ x) :
      HasType (((∅ : Context Atom).insert w a.dual).insert x a)
        (.link w x)
  | cut {Γ Δ : Context Atom} {a : Logic.CLL.Proposition Atom}
      {p q : Proc Atom}
      (hp : HasType ((Γ.lift).insert (.var 0) a) p)
      (hq : HasType ((Δ.lift).insert (.var 0) a.dual) q)
      (hdisj : Finmap.Disjoint Γ Δ) :
      HasType (Γ ∪ Δ) (.cut a p q)
  | tensor {Γ Δ : Context Atom} {x : PiCalculus.Name}
      {a b : Logic.CLL.Proposition Atom} {p q : Proc Atom}
      (hp : HasType ((Γ.lift).insert (.var 0) a) p)
      (hq : HasType (Δ.insert x b) q)
      (hdisj : Finmap.Disjoint Γ Δ) (hxΓ : x ∉ Γ) (hxΔ : x ∉ Δ) :
      HasType ((Γ ∪ Δ).insert x (.tensor a b)) (.output x p q)
  | parr {Γ : Context Atom} {x : PiCalculus.Name}
      {a b : Logic.CLL.Proposition Atom} {p : Proc Atom}
      (hp : HasType
        (((Γ.lift).insert (.var 0) a).insert
          (PiCalculus.liftName 0 x) b) p)
      (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x (.parr a b)) (.input x p)
  | oplusLeft {Γ : Context Atom} {x : PiCalculus.Name}
      {a b : Logic.CLL.Proposition Atom} {p : Proc Atom}
      (hp : HasType (Γ.insert x a) p) (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x (.oplus a b)) (.selectLeft x p)
  | oplusRight {Γ : Context Atom} {x : PiCalculus.Name}
      {a b : Logic.CLL.Proposition Atom} {p : Proc Atom}
      (hp : HasType (Γ.insert x b) p) (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x (.oplus a b)) (.selectRight x p)
  | with {Γ : Context Atom} {x : PiCalculus.Name}
      {a b : Logic.CLL.Proposition Atom} {p q : Proc Atom}
      (hp : HasType (Γ.insert x a) p)
      (hq : HasType (Γ.insert x b) q) (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x (.with a b)) (.choice x p q)
  | one {x : PiCalculus.Name} :
      HasType ((∅ : Context Atom).insert x .one) (.emptyOutput x)
  | bot {Γ : Context Atom} {x : PiCalculus.Name} {p : Proc Atom}
      (hp : HasType Γ p) (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x .bot) (.emptyInput x p)
  | top {Γ : Context Atom} {x : PiCalculus.Name} (hxΓ : x ∉ Γ) :
      HasType (Γ.insert x .top) (.emptyChoice x)

/-- Erasing a typed CP process and its channel names yields a derivable
one-sided CLL sequent. -/
theorem HasType.derivable_eraseNames {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) : Logic.InferenceSystem.Derivable Γ.eraseNames := by
  have hins : ∀ (Δ : Context Atom) (k : PiCalculus.Name)
      (v : Logic.CLL.Proposition Atom), k ∉ Δ →
      Context.eraseNames (Δ.insert k v) = v ::ₘ Δ.eraseNames := by
    intro Δ k v hk
    simp only [Context.eraseNames, Finmap.entries_insert_of_notMem hk,
      Multiset.map_cons]
  have hlift : ∀ Δ : Context Atom, Δ.lift.eraseNames = Δ.eraseNames := by
    intro Δ
    simp only [Context.eraseNames, Context.lift, Context.mapKeys,
      Multiset.map_map]
    rfl
  have hunion : ∀ Δ₁ Δ₂ : Context Atom, Finmap.Disjoint Δ₁ Δ₂ →
      Context.eraseNames (Δ₁ ∪ Δ₂) = Δ₁.eraseNames + Δ₂.eraseNames := by
    intro Δ₁ Δ₂ hdisj
    have hdis : Disjoint Δ₁.entries Δ₂.entries := by
      refine Multiset.disjoint_left.mpr ?_
      intro e he1 he2
      obtain ⟨k, v⟩ := e
      have hk1 : k ∈ Δ₁ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he1
      have hk2 : k ∈ Δ₂ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he2
      exact hdisj k hk1 hk2
    have hentries : (Δ₁ ∪ Δ₂).entries = Δ₁.entries + Δ₂.entries := by
      rw [Multiset.Nodup.ext (Finmap.nodup_entries _)
        (Multiset.nodup_add.2 ⟨Finmap.nodup_entries _,
          Finmap.nodup_entries _, hdis⟩)]
      rintro ⟨k, v⟩
      rw [Multiset.mem_add, ← Finmap.mem_lookup_iff,
        ← Finmap.mem_lookup_iff, ← Finmap.mem_lookup_iff,
        Finmap.mem_lookup_union]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨fun hk => hdisj k hk
            (Finmap.mem_of_lookup_eq_some h), h⟩
    simp only [Context.eraseNames, hentries, Multiset.map_add]
  have hl0ne : ∀ x : PiCalculus.Name, PiCalculus.liftName 0 x ≠ .var 0 := by
    intro x hx
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, reduceCtorEq] at hx
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
          PiCalculus.Name.var.injEq, Nat.add_eq_zero_iff, one_ne_zero,
          and_false] at hx
  have hl0inj : Function.Injective (PiCalculus.liftName 0) := by
    intro x y hxy
    cases x <;> cases y <;>
      simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, reduceCtorEq,
        PiCalculus.Name.const.injEq, PiCalculus.Name.var.injEq,
        Nat.add_right_cancel_iff] at hxy ⊢ <;>
      exact hxy
  have hmem : ∀ (Δ : Context Atom) (y : PiCalculus.Name),
      y ∈ Δ.lift ↔ ∃ x ∈ Δ, PiCalculus.liftName 0 x = y := by
    intro Δ y
    simp only [Finmap.mem_def, Context.lift, Context.mapKeys,
      Multiset.keys, Multiset.map_map, Function.comp_def,
      Multiset.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.1, ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
  have hvar0 : ∀ Δ : Context Atom, (PiCalculus.Name.var 0) ∉ Δ.lift := by
    intro Δ h
    obtain ⟨x, hx, hxy⟩ := (hmem Δ _).mp h
    exact hl0ne x hxy
  induction h with
  | @ax w x a hwx =>
      have hx : x ∉ (∅ : Context Atom).insert w a.dual := by
        intro h
        rw [Finmap.mem_insert] at h
        obtain h | h := h
        · exact hwx h.symm
        · exact Finmap.notMem_empty h
      rw [hins _ _ _ hx, hins _ _ _ Finmap.notMem_empty]
      exact ⟨Logic.CLL.Proof.ax⟩
  | @cut Γ Δ a p q hp hq hdisj ihp ihq =>
      rw [hins _ _ _ (hvar0 _), hlift] at ihp
      rw [hins _ _ _ (hvar0 _), hlift] at ihq
      rw [hunion _ _ hdisj]
      obtain ⟨dp⟩ := ihp
      obtain ⟨dq⟩ := ihq
      exact ⟨Logic.CLL.Proof.cut dp dq⟩
  | @tensor Γ Δ x a b p q hp hq hdisj hxΓ hxΔ ihp ihq =>
      rw [hins _ _ _ (hvar0 _), hlift] at ihp
      rw [hins _ _ _ hxΔ] at ihq
      have hx : x ∉ Γ ∪ Δ := by
        intro h
        rw [Finmap.mem_union] at h
        obtain h | h := h
        · exact hxΓ h
        · exact hxΔ h
      rw [hins _ _ _ hx, hunion _ _ hdisj]
      obtain ⟨dp⟩ := ihp
      obtain ⟨dq⟩ := ihq
      exact ⟨Logic.CLL.Proof.tensor dp dq⟩
  | @parr Γ x a b p hp hxΓ ihp =>
      have hfresh : PiCalculus.liftName 0 x ∉ (Γ.lift).insert (.var 0) a := by
        intro h
        rw [Finmap.mem_insert] at h
        obtain h | h := h
        · exact hl0ne x h
        · obtain ⟨x₀, hx₀, heq⟩ := (hmem Γ _).mp h
          have heqx : x₀ = x := hl0inj heq
          rw [heqx] at hx₀
          exact hxΓ hx₀
      rw [hins _ _ _ hfresh, hins _ _ _ (hvar0 Γ), hlift] at ihp
      rw [hins _ _ _ hxΓ]
      obtain ⟨dp⟩ := ihp
      rw [Multiset.cons_swap] at dp
      exact ⟨Logic.CLL.Proof.parr dp⟩
  | @oplusLeft Γ x a b p hp hxΓ ihp =>
      rw [hins _ _ _ hxΓ] at ihp
      rw [hins _ _ _ hxΓ]
      obtain ⟨dp⟩ := ihp
      exact ⟨Logic.CLL.Proof.oplus₁ dp⟩
  | @oplusRight Γ x a b p hp hxΓ ihp =>
      rw [hins _ _ _ hxΓ] at ihp
      rw [hins _ _ _ hxΓ]
      obtain ⟨dp⟩ := ihp
      exact ⟨Logic.CLL.Proof.oplus₂ dp⟩
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
      rw [hins _ _ _ hxΓ] at ihp
      rw [hins _ _ _ hxΓ] at ihq
      rw [hins _ _ _ hxΓ]
      obtain ⟨dp⟩ := ihp
      obtain ⟨dq⟩ := ihq
      exact ⟨Logic.CLL.Proof.with dp dq⟩
  | @one x =>
      rw [hins _ _ _ Finmap.notMem_empty]
      exact ⟨Logic.CLL.Proof.one⟩
  | @bot Γ x p hp hxΓ ihp =>
      rw [hins _ _ _ hxΓ]
      obtain ⟨dp⟩ := ihp
      exact ⟨Logic.CLL.Proof.bot dp⟩
  | @top Γ x hxΓ =>
      rw [hins _ _ _ hxΓ]
      exact ⟨Logic.CLL.Proof.top⟩

/-- CP typing is invariant under injective renaming of channel names. -/
theorem HasType.rename {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) :
    HasType (Γ.mapKeys f hf) (p.rename f) := by
  have hlr : ∀ (g : PiCalculus.Name → PiCalculus.Name) (x : PiCalculus.Name),
      liftRename g (PiCalculus.liftName 0 x) = PiCalculus.liftName 0 (g x) := by
    intro g x
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, liftRename]
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, liftRename]
  have hl0inj : Function.Injective (PiCalculus.liftName 0) := by
    intro x y hxy
    cases x <;> cases y <;>
      simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, reduceCtorEq,
        PiCalculus.Name.const.injEq, PiCalculus.Name.var.injEq,
        Nat.add_right_cancel_iff] at hxy ⊢ <;>
      exact hxy
  have hl0ne : ∀ x : PiCalculus.Name, PiCalculus.liftName 0 x ≠ .var 0 := by
    intro x hx
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, reduceCtorEq] at hx
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
          PiCalculus.Name.var.injEq, Nat.add_eq_zero_iff, one_ne_zero,
          and_false] at hx
  have hlinj : ∀ g : PiCalculus.Name → PiCalculus.Name,
      Function.Injective g → Function.Injective (liftRename g) := by
    intro g hg x y hxy
    rcases x with n | _ | i <;> rcases y with m | _ | j <;>
      simp only [liftRename] at hxy
    · exact hg (hl0inj hxy)
    · exact absurd hxy (hl0ne _)
    · exact absurd (hg (hl0inj hxy)) (by intro hc; cases hc)
    · exact absurd hxy.symm (hl0ne _)
    · rfl
    · exact absurd hxy.symm (hl0ne _)
    · exact absurd (hg (hl0inj hxy)) (by intro hc; cases hc)
    · exact absurd hxy (hl0ne _)
    · cases hg (hl0inj hxy); rfl
  have hmemK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ : Context Atom) (y : PiCalculus.Name),
      y ∈ Δ.mapKeys g hg ↔ ∃ x ∈ Δ, g x = y := by
    intro g hg Δ y
    simp only [Finmap.mem_def, Context.mapKeys, Multiset.keys,
      Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.1, ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
  have hnotK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ : Context Atom)
      (x : PiCalculus.Name), x ∉ Δ → g x ∉ Δ.mapKeys g hg := by
    intro g hg Δ x hx h
    obtain ⟨y, hy, hyx⟩ := (hmemK g hg Δ _).mp h
    exact hx (hg hyx ▸ hy)
  have hvar0 : ∀ Δ : Context Atom, (PiCalculus.Name.var 0) ∉ Δ.lift := by
    intro Δ h
    obtain ⟨x, _, hx⟩ := (hmemK _ _ Δ _).mp h
    exact hl0ne x hx
  have hinsK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ : Context Atom)
      (k : PiCalculus.Name) (v : Logic.CLL.Proposition Atom),
      k ∉ Δ → Context.mapKeys g hg (Δ.insert k v) =
        (Δ.mapKeys g hg).insert (g k) v := by
    intro g hg Δ k v hk
    apply Finmap.ext
    rw [Finmap.entries_insert_of_notMem (hnotK g hg Δ k hk)]
    simp only [Context.mapKeys, Finmap.entries_insert_of_notMem hk,
      Multiset.map_cons]
  have hunionE : ∀ Δ₁ Δ₂ : Context Atom, Finmap.Disjoint Δ₁ Δ₂ →
      (Δ₁ ∪ Δ₂).entries = Δ₁.entries + Δ₂.entries := by
    intro Δ₁ Δ₂ hd
    have hdis : Disjoint Δ₁.entries Δ₂.entries := by
      refine Multiset.disjoint_left.mpr ?_
      intro e he1 he2
      obtain ⟨k, v⟩ := e
      have hk1 : k ∈ Δ₁ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he1
      have hk2 : k ∈ Δ₂ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he2
      exact hd k hk1 hk2
    rw [Multiset.Nodup.ext (Finmap.nodup_entries _)
      (Multiset.nodup_add.2 ⟨Finmap.nodup_entries _,
        Finmap.nodup_entries _, hdis⟩)]
    rintro ⟨k, v⟩
    rw [Multiset.mem_add, ← Finmap.mem_lookup_iff,
      ← Finmap.mem_lookup_iff, ← Finmap.mem_lookup_iff,
      Finmap.mem_lookup_union]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨fun hk => hd k hk
          (Finmap.mem_of_lookup_eq_some h), h⟩
  have hdisjK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ₁ Δ₂ : Context Atom),
      Finmap.Disjoint Δ₁ Δ₂ →
      Finmap.Disjoint (Δ₁.mapKeys g hg) (Δ₂.mapKeys g hg) := by
    intro g hg Δ₁ Δ₂ hd y hy1 hy2
    obtain ⟨x₁, hx₁, rfl⟩ := (hmemK g hg Δ₁ y).mp hy1
    obtain ⟨x₂, hx₂, hx⟩ := (hmemK g hg Δ₂ _).mp hy2
    exact hd x₁ hx₁ (hg hx ▸ hx₂)
  have hunionK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ₁ Δ₂ : Context Atom),
      Finmap.Disjoint Δ₁ Δ₂ →
      Context.mapKeys g hg (Δ₁ ∪ Δ₂) = Δ₁.mapKeys g hg ∪ Δ₂.mapKeys g hg := by
    intro g hg Δ₁ Δ₂ hd
    apply Finmap.ext
    rw [hunionE _ _ (hdisjK g hg Δ₁ Δ₂ hd)]
    simp only [Context.mapKeys, hunionE _ _ hd, Multiset.map_add]
  have hliftK : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (hg : Function.Injective g) (Δ : Context Atom),
      Context.mapKeys (liftRename g) (hlinj g hg) Δ.lift = (Δ.mapKeys g hg).lift := by
    intro g hg Δ
    apply Finmap.ext
    simp only [Context.lift, Context.mapKeys, Multiset.map_map,
      Function.comp_def, hlr]
  have hlr0 : ∀ g : PiCalculus.Name → PiCalculus.Name,
      liftRename g (.var 0) = .var 0 := fun _ => rfl
  induction h generalizing f with
  | @ax w x a hwx =>
      have hx : x ∉ (∅ : Context Atom).insert w a.dual := by
        intro h
        rw [Finmap.mem_insert] at h
        obtain h | h := h
        · exact hwx h.symm
        · exact Finmap.notMem_empty h
      rw [hinsK _ _ _ _ _ hx, hinsK _ _ _ _ _ Finmap.notMem_empty]
      exact HasType.ax (hf.ne hwx)
  | @cut Γ Δ a p q hp hq hdisj ihp ihq =>
      have hp' := ihp (hlinj f hf)
      have hq' := ihq (hlinj f hf)
      rw [hinsK _ _ _ _ _ (hvar0 _), hliftK f hf, hlr0] at hp'
      rw [hinsK _ _ _ _ _ (hvar0 _), hliftK f hf, hlr0] at hq'
      rw [hunionK _ _ _ _ hdisj]
      exact HasType.cut hp' hq' (hdisjK _ _ _ _ hdisj)
  | @tensor Γ Δ x a b p q hp hq hdisj hxΓ hxΔ ihp ihq =>
      have hx : x ∉ Γ ∪ Δ := by
        intro h
        rw [Finmap.mem_union] at h
        obtain h | h := h
        · exact hxΓ h
        · exact hxΔ h
      have hp' := ihp (hlinj f hf)
      have hq' := ihq hf
      rw [hinsK _ _ _ _ _ (hvar0 _), hliftK f hf, hlr0] at hp'
      rw [hinsK _ _ _ _ _ hxΔ] at hq'
      rw [hinsK _ _ _ _ _ hx, hunionK _ _ _ _ hdisj]
      exact HasType.tensor hp' hq' (hdisjK _ _ _ _ hdisj) (hnotK _ _ _ _ hxΓ)
        (hnotK _ _ _ _ hxΔ)
  | @parr Γ x a b p hp hxΓ ihp =>
      have hx : PiCalculus.liftName 0 x ∉ (Γ.lift).insert (.var 0) a := by
        intro h
        rw [Finmap.mem_insert] at h
        obtain h | h := h
        · exact hl0ne x h
        · obtain ⟨y, hy, hyx⟩ := (hmemK _ _ Γ _).mp h
          exact hxΓ (hl0inj hyx ▸ hy)
      have hp' := ihp (hlinj f hf)
      rw [hinsK _ _ _ _ _ hx, hinsK _ _ _ _ _ (hvar0 Γ), hliftK f hf, hlr0,
        hlr] at hp'
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.parr hp' (hnotK _ _ _ _ hxΓ)
  | @oplusLeft Γ x a b p hp hxΓ ihp =>
      have hp' := ihp hf
      rw [hinsK _ _ _ _ _ hxΓ] at hp'
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.oplusLeft hp' (hnotK _ _ _ _ hxΓ)
  | @oplusRight Γ x a b p hp hxΓ ihp =>
      have hp' := ihp hf
      rw [hinsK _ _ _ _ _ hxΓ] at hp'
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.oplusRight hp' (hnotK _ _ _ _ hxΓ)
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
      have hp' := ihp hf
      have hq' := ihq hf
      rw [hinsK _ _ _ _ _ hxΓ] at hp' hq'
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.with hp' hq' (hnotK _ _ _ _ hxΓ)
  | @one x =>
      rw [hinsK _ _ _ _ _ Finmap.notMem_empty]
      exact HasType.one
  | @bot Γ x p hp hxΓ ihp =>
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.bot (ihp hf) (hnotK _ _ _ _ hxΓ)
  | @top Γ x hxΓ =>
      rw [hinsK _ _ _ _ _ hxΓ]
      exact HasType.top (hnotK _ _ _ _ hxΓ)

/-- Substitution for the channel bound by a cut preserves typing,
provided the substituted channel is not already in the remaining
environment. -/
theorem HasType.subst {Γ : Context Atom} {a : Logic.CLL.Proposition Atom}
    {p : Proc Atom} {w : PiCalculus.Name}
    (hp : HasType ((Γ.lift).insert (.var 0) a) p) (hw : w ∉ Γ) :
    HasType (Γ.insert w a) (p.subst w) := by
  have hl0inj : Function.Injective (PiCalculus.liftName 0) := by
    intro x y hxy
    cases x <;> cases y <;>
      simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, reduceCtorEq,
        PiCalculus.Name.const.injEq, PiCalculus.Name.var.injEq,
        Nat.add_right_cancel_iff] at hxy ⊢ <;>
      exact hxy
  have hl0ne : ∀ x : PiCalculus.Name, PiCalculus.liftName 0 x ≠ .var 0 := by
    intro x hx
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, reduceCtorEq] at hx
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
          PiCalculus.Name.var.injEq, Nat.add_eq_zero_iff, one_ne_zero,
          and_false] at hx
  have hlr : ∀ (g : PiCalculus.Name → PiCalculus.Name) (x : PiCalculus.Name),
      liftRename g (PiCalculus.liftName 0 x) = PiCalculus.liftName 0 (g x) := by
    intro g x
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, liftRename]
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, liftRename]
  have hlr0 : ∀ g : PiCalculus.Name → PiCalculus.Name,
      liftRename g (.var 0) = .var 0 := fun _ => rfl
  have hmemL : ∀ (Δ : Context Atom) (y : PiCalculus.Name),
      y ∈ Δ.lift ↔ ∃ x ∈ Δ, PiCalculus.liftName 0 x = y := by
    intro Δ y
    simp only [Finmap.mem_def, Context.lift, Context.mapKeys,
      Multiset.keys, Multiset.map_map, Function.comp_def,
      Multiset.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.1, ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
  have hvar0 : ∀ Δ : Context Atom, (PiCalculus.Name.var 0) ∉ Δ.lift := by
    intro Δ h
    obtain ⟨x, hx, hxy⟩ := (hmemL Δ _).mp h
    exact hl0ne x hxy
  have hunionE : ∀ Δ₁ Δ₂ : Context Atom, Finmap.Disjoint Δ₁ Δ₂ →
      (Δ₁ ∪ Δ₂).entries = Δ₁.entries + Δ₂.entries := by
    intro Δ₁ Δ₂ hd
    have hdis : Disjoint Δ₁.entries Δ₂.entries := by
      refine Multiset.disjoint_left.mpr ?_
      intro e he1 he2
      obtain ⟨k, v⟩ := e
      have hk1 : k ∈ Δ₁ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he1
      have hk2 : k ∈ Δ₂ := by
        rw [Finmap.mem_def]
        exact Multiset.mem_map_of_mem Sigma.fst he2
      exact hd k hk1 hk2
    rw [Multiset.Nodup.ext (Finmap.nodup_entries _)
      (Multiset.nodup_add.2 ⟨Finmap.nodup_entries _,
        Finmap.nodup_entries _, hdis⟩)]
    rintro ⟨k, v⟩
    rw [Multiset.mem_add, ← Finmap.mem_lookup_iff,
      ← Finmap.mem_lookup_iff, ← Finmap.mem_lookup_iff,
      Finmap.mem_lookup_union]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨fun hk => hd k hk
          (Finmap.mem_of_lookup_eq_some h), h⟩
  have hmk : ∀ (g : PiCalculus.Name → PiCalculus.Name) (Δ : Context Atom),
      (∀ x ∈ Δ, ∀ y ∈ Δ, g x = g y → x = y) →
      ∃ Δ' : Context Atom,
        Δ'.entries = Δ.entries.map (fun e => ⟨g e.1, e.2⟩) := by
    intro g Δ hg
    refine ⟨⟨Δ.entries.map _, ?_⟩, rfl⟩
    rw [← Multiset.nodup_keys]
    have hnd := Δ.nodupKeys.nodup_keys
    have hinjK : ∀ x ∈ Δ.entries.keys, ∀ y ∈ Δ.entries.keys,
        g x = g y → x = y := by
      intro x hx y hy hxy
      exact hg x hx y hy hxy
    have hmap := hnd.map_on (f := g) hinjK
    simpa only [Multiset.keys, Multiset.map_map,
      Function.comp_def] using hmap
  have hmemI : ∀ (g : PiCalculus.Name → PiCalculus.Name) (Δ Δ' : Context Atom),
      Δ'.entries = Δ.entries.map (fun e => ⟨g e.1, e.2⟩) →
      ∀ y, y ∈ Δ' ↔ ∃ x ∈ Δ, g x = y := by
    intro g Δ Δ' hentries y
    simp only [Finmap.mem_def, hentries, Multiset.keys, Multiset.map_map,
      Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.1, ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
  have himgIns : ∀ (g : PiCalculus.Name → PiCalculus.Name) (Δ Δ' : Context Atom)
      (k : PiCalculus.Name) (v : Logic.CLL.Proposition Atom),
      Δ'.entries = Δ.entries.map (fun e => ⟨g e.1, e.2⟩) → k ∉ Δ → g k ∉ Δ' →
      (Δ'.insert (g k) v).entries =
        (Δ.insert k v).entries.map (fun e => ⟨g e.1, e.2⟩) := by
    intro g Δ Δ' k v hentries hk hgk
    rw [Finmap.entries_insert_of_notMem hgk,
      Finmap.entries_insert_of_notMem hk, hentries, Multiset.map_cons]
  have himgLift : ∀ (g : PiCalculus.Name → PiCalculus.Name) (Δ Δ' : Context Atom),
      Δ'.entries = Δ.entries.map (fun e => ⟨g e.1, e.2⟩) →
      (Context.lift Δ').entries =
        (Context.lift Δ).entries.map (fun e => ⟨liftRename g e.1, e.2⟩) := by
    intro g Δ Δ' hentries
    simp only [Context.lift, Context.mapKeys, hentries, Multiset.map_map,
      Function.comp_def, hlr]
  have himgUnion : ∀ (g : PiCalculus.Name → PiCalculus.Name)
      (Δ₁ Δ₂ Δ₁' Δ₂' : Context Atom),
      Δ₁'.entries = Δ₁.entries.map (fun e => ⟨g e.1, e.2⟩) →
      Δ₂'.entries = Δ₂.entries.map (fun e => ⟨g e.1, e.2⟩) →
      Finmap.Disjoint Δ₁ Δ₂ → Finmap.Disjoint Δ₁' Δ₂' →
      (Δ₁' ∪ Δ₂').entries = (Δ₁ ∪ Δ₂).entries.map (fun e => ⟨g e.1, e.2⟩) := by
    intro g Δ₁ Δ₂ Δ₁' Δ₂' h1 h2 hd hd'
    rw [hunionE _ _ hd', hunionE _ _ hd, h1, h2, Multiset.map_add]
  have hinjL : ∀ (g : PiCalculus.Name → PiCalculus.Name) (Δ : Context Atom),
      (∀ x ∈ Δ, ∀ y ∈ Δ, g x = g y → x = y) →
      ∀ x, (x = .var 0 ∨ ∃ x₀ ∈ Δ, PiCalculus.liftName 0 x₀ = x) →
      ∀ y, (y = .var 0 ∨ ∃ y₀ ∈ Δ, PiCalculus.liftName 0 y₀ = y) →
      liftRename g x = liftRename g y → x = y := by
    intro g Δ hg x hx y hy hxy
    rcases hx with rfl | ⟨x₀, hx₀, rfl⟩
    · rcases hy with rfl | ⟨y₀, hy₀, rfl⟩
      · rfl
      · rw [hlr0, hlr] at hxy
        exact (hl0ne _ hxy.symm).elim
    · rcases hy with rfl | ⟨y₀, hy₀, rfl⟩
      · rw [hlr0, hlr] at hxy
        exact (hl0ne _ hxy).elim
      · rw [hlr, hlr] at hxy
        have heq : g x₀ = g y₀ := hl0inj hxy
        have heqx : x₀ = y₀ := hg x₀ hx₀ y₀ hy₀ heq
        rw [heqx]
  have key : ∀ {Δ : Context Atom} {q : Proc Atom}, HasType Δ q →
      ∀ (g : PiCalculus.Name → PiCalculus.Name),
      (∀ x ∈ Δ, ∀ y ∈ Δ, g x = g y → x = y) →
      ∀ Δ' : Context Atom, Δ'.entries = Δ.entries.map (fun e => ⟨g e.1, e.2⟩) →
      HasType Δ' (q.rename g) := by
    intro Δ q hΔq
    induction hΔq with
    | @ax w x a hwx =>
        intro g hg Δ' hΔ'
        have hwS : w ∈ (∅ : Context Atom).insert w a.dual :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hxO : x ∈ (((∅ : Context Atom).insert w a.dual).insert x a) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hwO : w ∈ (((∅ : Context Atom).insert w a.dual).insert x a) :=
          Finmap.mem_insert.2 (Or.inr hwS)
        have hwx' : g w ≠ g x := fun heq => hwx (hg w hwO x hxO heq)
        have hgE : ∀ x ∈ (∅ : Context Atom), ∀ y ∈ (∅ : Context Atom), g x = g y → x = y := by
          intro x hx y hy hxy
          exact (Finmap.notMem_empty hx).elim
        obtain ⟨E', hE'⟩ := hmk g (∅ : Context Atom) hgE
        have hwE' : g w ∉ E' := by
          intro h
          obtain ⟨y, hy, _⟩ := (hmemI g ∅ E' hE' _).mp h
          exact Finmap.notMem_empty hy
        have hS' : (E'.insert (g w) a.dual).entries =
            ((∅ : Context Atom).insert w a.dual).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g ∅ E' w a.dual hE' Finmap.notMem_empty hwE'
        have hxS : x ∉ (∅ : Context Atom).insert w a.dual := by
          intro h
          rw [Finmap.mem_insert] at h
          obtain h | h := h
          · exact hwx h.symm
          · exact Finmap.notMem_empty h
        have hxS' : g x ∉ E'.insert (g w) a.dual := by
          intro h
          rw [Finmap.mem_insert] at h
          obtain h | h := h
          · exact hwx (hg x hxO w hwO h).symm
          · obtain ⟨y, hy, _⟩ := (hmemI g ∅ E' hE' _).mp h
            exact Finmap.notMem_empty hy
        have hO' : ((E'.insert (g w) a.dual).insert (g x) a).entries =
            ((((∅ : Context Atom).insert w a.dual).insert x a)).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g _ _ x a hS' hxS hxS'
        have hE'empty : E' = ∅ := by
          apply Finmap.ext
          rw [hE']
          rfl
        rw [hE'empty] at hO'
        have heq : Δ' =
            (((∅ : Context Atom).insert (g w) a.dual).insert (g x) a) := by
          apply Finmap.ext
          rw [hΔ', hO']
        rw [heq]
        exact HasType.ax hwx'
    | @cut Γ Δ a p q hp hq hdisj ihp ihq =>
        intro g hg Δ' hΔ'
        have hsubΓ : ∀ k ∈ Γ, k ∈ Γ ∪ Δ := fun k hk =>
          Finmap.mem_union.2 (Or.inl hk)
        have hsubΔ : ∀ k ∈ Δ, k ∈ Γ ∪ Δ := fun k hk =>
          Finmap.mem_union.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsubΓ x hx) y (hsubΓ y hy) hxy
        have hgΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsubΔ x hx) y (hsubΔ y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        obtain ⟨D', hD'⟩ := hmk g Δ hgΔ
        have hd' : Finmap.Disjoint Γ' D' := by
          intro y hy1 hy2
          obtain ⟨x₁, hx₁, rfl⟩ := (hmemI g Γ Γ' hΓ' y).mp hy1
          obtain ⟨x₂, hx₂, heq⟩ := (hmemI g Δ D' hD' _).mp hy2
          have heqx : x₁ = x₂ :=
            hg x₁ (hsubΓ x₁ hx₁) x₂ (hsubΔ x₂ hx₂) heq.symm
          subst heqx
          exact hdisj _ hx₁ hx₂
        have hun : (Γ' ∪ D').entries =
            (Γ ∪ Δ).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgUnion g Γ Δ Γ' D' hΓ' hD' hdisj hd'
        have heq : Δ' = Γ' ∪ D' := by
          apply Finmap.ext
          rw [hΔ', hun]
        have hLiftΓ : (Context.lift Γ').entries =
            (Context.lift Γ).entries.map
              (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgLift g Γ Γ' hΓ'
        have hLiftΔ : (Context.lift D').entries =
            (Context.lift Δ).entries.map
              (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgLift g Δ D' hD'
        have hgkΓ : liftRename g (.var 0) ∉ Context.lift Γ' := by
          rw [hlr0]
          exact hvar0 Γ'
        have hgkΔ : liftRename g (.var 0) ∉ Context.lift D' := by
          rw [hlr0]
          exact hvar0 D'
        have hInsΓ :
            ((Context.lift Γ').insert (liftRename g (.var 0)) a).entries =
              (((Γ.lift).insert (.var 0) a)).entries.map
                (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgIns (liftRename g) _ _ (.var 0) a hLiftΓ (hvar0 Γ) hgkΓ
        have hInsΔ :
            ((Context.lift D').insert (liftRename g (.var 0)) a.dual).entries =
              (((Δ.lift).insert (.var 0) a.dual)).entries.map
                (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgIns (liftRename g) _ _ (.var 0) a.dual hLiftΔ (hvar0 Δ) hgkΔ
        rw [hlr0] at hInsΓ hInsΔ
        have hgPΓ : ∀ x ∈ ((Γ.lift).insert (.var 0) a),
            ∀ y ∈ ((Γ.lift).insert (.var 0) a),
            liftRename g x = liftRename g y → x = y := by
          intro x hx y hy hxy
          have hx' :
              x = .var 0 ∨ ∃ x₀ ∈ Γ, PiCalculus.liftName 0 x₀ = x := by
            rw [Finmap.mem_insert] at hx
            obtain rfl | hx := hx
            · exact Or.inl rfl
            · obtain ⟨x₀, hx₀, heq⟩ := (hmemL Γ _).mp hx
              exact Or.inr ⟨x₀, hx₀, heq⟩
          have hy' :
              y = .var 0 ∨ ∃ y₀ ∈ Γ, PiCalculus.liftName 0 y₀ = y := by
            rw [Finmap.mem_insert] at hy
            obtain rfl | hy := hy
            · exact Or.inl rfl
            · obtain ⟨y₀, hy₀, heq⟩ := (hmemL Γ _).mp hy
              exact Or.inr ⟨y₀, hy₀, heq⟩
          exact hinjL g Γ hgΓ x hx' y hy' hxy
        have hgPΔ : ∀ x ∈ ((Δ.lift).insert (.var 0) a.dual),
            ∀ y ∈ ((Δ.lift).insert (.var 0) a.dual),
            liftRename g x = liftRename g y → x = y := by
          intro x hx y hy hxy
          have hx' :
              x = .var 0 ∨ ∃ x₀ ∈ Δ, PiCalculus.liftName 0 x₀ = x := by
            rw [Finmap.mem_insert] at hx
            obtain rfl | hx := hx
            · exact Or.inl rfl
            · obtain ⟨x₀, hx₀, heq⟩ := (hmemL Δ _).mp hx
              exact Or.inr ⟨x₀, hx₀, heq⟩
          have hy' :
              y = .var 0 ∨ ∃ y₀ ∈ Δ, PiCalculus.liftName 0 y₀ = y := by
            rw [Finmap.mem_insert] at hy
            obtain rfl | hy := hy
            · exact Or.inl rfl
            · obtain ⟨y₀, hy₀, heq⟩ := (hmemL Δ _).mp hy
              exact Or.inr ⟨y₀, hy₀, heq⟩
          exact hinjL g Δ hgΔ x hx' y hy' hxy
        have hp' : HasType ((Γ'.lift).insert (.var 0) a)
            (p.rename (liftRename g)) :=
          ihp (liftRename g) hgPΓ _ hInsΓ
        have hq' : HasType ((D'.lift).insert (.var 0) a.dual)
            (q.rename (liftRename g)) :=
          ihq (liftRename g) hgPΔ _ hInsΔ
        rw [heq]
        exact HasType.cut hp' hq' hd'
    | @tensor Γ Δ x a b p q hp hq hdisj hxΓ hxΔ ihp ihq =>
        intro g hg Δ' hΔ'
        have hxU : x ∉ Γ ∪ Δ := by
          intro h
          rw [Finmap.mem_union] at h
          obtain h | h := h
          · exact hxΓ h
          · exact hxΔ h
        have hxO : x ∈ (Γ ∪ Δ).insert x (.tensor a b) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsubΓ : ∀ k ∈ Γ, k ∈ (Γ ∪ Δ).insert x (.tensor a b) := fun k hk =>
          Finmap.mem_insert.2
            (Or.inr (Finmap.mem_union.2 (Or.inl hk)))
        have hsubΔ : ∀ k ∈ Δ, k ∈ (Γ ∪ Δ).insert x (.tensor a b) := fun k hk =>
          Finmap.mem_insert.2
            (Or.inr (Finmap.mem_union.2 (Or.inr hk)))
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsubΓ x hx) y (hsubΓ y hy) hxy
        have hgΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsubΔ x hx) y (hsubΔ y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        obtain ⟨D', hD'⟩ := hmk g Δ hgΔ
        have hd' : Finmap.Disjoint Γ' D' := by
          intro y hy1 hy2
          obtain ⟨x₁, hx₁, rfl⟩ := (hmemI g Γ Γ' hΓ' y).mp hy1
          obtain ⟨x₂, hx₂, heq⟩ := (hmemI g Δ D' hD' _).mp hy2
          have heqx : x₁ = x₂ :=
            hg x₁ (hsubΓ x₁ hx₁) x₂ (hsubΔ x₂ hx₂) heq.symm
          subst heqx
          exact hdisj _ hx₁ hx₂
        have hun : (Γ' ∪ D').entries =
            (Γ ∪ Δ).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgUnion g Γ Δ Γ' D' hΓ' hD' hdisj hd'
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsubΓ y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hxD' : g x ∉ D' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Δ D' hD' _).mp h
          have heqy : y = x := hg y (hsubΔ y hy) x hxO heq
          subst heqy
          exact hxΔ hy
        have hxU' : g x ∉ Γ' ∪ D' := by
          intro h
          rw [Finmap.mem_union] at h
          obtain h | h := h
          · exact hxG' h
          · exact hxD' h
        have hOuter : ((Γ' ∪ D').insert (g x) (.tensor a b)).entries =
            (((Γ ∪ Δ).insert x (.tensor a b))).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g _ _ x (.tensor a b) hun hxU hxU'
        have heq : Δ' = (Γ' ∪ D').insert (g x) (.tensor a b) := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hLiftΓ : (Context.lift Γ').entries =
            (Context.lift Γ).entries.map
              (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgLift g Γ Γ' hΓ'
        have hgkΓ : liftRename g (.var 0) ∉ Context.lift Γ' := by
          rw [hlr0]
          exact hvar0 Γ'
        have hInsΓ :
            ((Context.lift Γ').insert (liftRename g (.var 0)) a).entries =
              (((Γ.lift).insert (.var 0) a)).entries.map
                (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgIns (liftRename g) _ _ (.var 0) a hLiftΓ (hvar0 Γ) hgkΓ
        rw [hlr0] at hInsΓ
        have hgPΓ : ∀ x ∈ ((Γ.lift).insert (.var 0) a),
            ∀ y ∈ ((Γ.lift).insert (.var 0) a),
            liftRename g x = liftRename g y → x = y := by
          intro x hx y hy hxy
          have hx' :
              x = .var 0 ∨ ∃ x₀ ∈ Γ, PiCalculus.liftName 0 x₀ = x := by
            rw [Finmap.mem_insert] at hx
            obtain rfl | hx := hx
            · exact Or.inl rfl
            · obtain ⟨x₀, hx₀, heq⟩ := (hmemL Γ _).mp hx
              exact Or.inr ⟨x₀, hx₀, heq⟩
          have hy' :
              y = .var 0 ∨ ∃ y₀ ∈ Γ, PiCalculus.liftName 0 y₀ = y := by
            rw [Finmap.mem_insert] at hy
            obtain rfl | hy := hy
            · exact Or.inl rfl
            · obtain ⟨y₀, hy₀, heq⟩ := (hmemL Γ _).mp hy
              exact Or.inr ⟨y₀, hy₀, heq⟩
          exact hinjL g Γ hgΓ x hx' y hy' hxy
        have hp' : HasType ((Γ'.lift).insert (.var 0) a)
            (p.rename (liftRename g)) :=
          ihp (liftRename g) hgPΓ _ hInsΓ
        have hsubP : ∀ k ∈ Δ.insert x b,
            k ∈ (Γ ∪ Δ).insert x (.tensor a b) := by
          intro k hk
          rw [Finmap.mem_insert] at hk
          obtain rfl | hk := hk
          · exact hxO
          · exact hsubΔ k hk
        have hgPΔ : ∀ k ∈ Δ.insert x b, ∀ l ∈ Δ.insert x b,
            g k = g l → k = l := fun k hk l hl hkl =>
          hg k (hsubP k hk) l (hsubP l hl) hkl
        have hPΔ' : (D'.insert (g x) b).entries =
            ((Δ.insert x b)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Δ D' x b hD' hxΔ hxD'
        have hq' : HasType (D'.insert (g x) b) (q.rename g) :=
          ihq g hgPΔ _ hPΔ'
        rw [heq]
        exact HasType.tensor hp' hq' hd' hxG' hxD'
    | @parr Γ x a b p hp hxΓ ihp =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x (.parr a b) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x (.parr a b) := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) (.parr a b)).entries =
            ((Γ.insert x (.parr a b))).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x (.parr a b) hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) (.parr a b) := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hLift : (Context.lift Γ').entries =
            (Context.lift Γ).entries.map
              (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgLift g Γ Γ' hΓ'
        have hgk0 : liftRename g (.var 0) ∉ Context.lift Γ' := by
          rw [hlr0]
          exact hvar0 Γ'
        have hIns0 :
            ((Context.lift Γ').insert (liftRename g (.var 0)) a).entries =
              (((Γ.lift).insert (.var 0) a)).entries.map
                (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgIns (liftRename g) _ _ (.var 0) a hLift (hvar0 Γ) hgk0
        rw [hlr0] at hIns0
        have hfresh :
            PiCalculus.liftName 0 x ∉ (Γ.lift).insert (.var 0) a := by
          intro h
          rw [Finmap.mem_insert] at h
          obtain h | h := h
          · exact hl0ne x h
          · obtain ⟨y, hy, heq⟩ := (hmemL Γ _).mp h
            have heqy : y = x := hl0inj heq
            subst heqy
            exact hxΓ hy
        have hfresh' :
            PiCalculus.liftName 0 (g x) ∉ (Γ'.lift).insert (.var 0) a := by
          intro h
          rw [Finmap.mem_insert] at h
          obtain h | h := h
          · exact hl0ne _ h
          · obtain ⟨y, hy, heq⟩ := (hmemL Γ' _).mp h
            have heqy : y = g x := hl0inj heq
            subst heqy
            exact hxG' hy
        have hgk1 : liftRename g (PiCalculus.liftName 0 x) ∉
            (Γ'.lift).insert (.var 0) a := by
          rw [hlr]
          exact hfresh'
        have hIns1 : ((((Γ'.lift).insert (.var 0) a).insert
            (liftRename g (PiCalculus.liftName 0 x)) b)).entries =
              ((((Γ.lift).insert (.var 0) a).insert
                (PiCalculus.liftName 0 x) b)).entries.map
                (fun e => ⟨liftRename g e.1, e.2⟩) :=
          himgIns (liftRename g) _ _ (PiCalculus.liftName 0 x) b
            hIns0 hfresh hgk1
        rw [hlr] at hIns1
        have hgP : ∀ k ∈ ((((Γ.lift).insert (.var 0) a).insert
            (PiCalculus.liftName 0 x) b)),
            ∀ l ∈ ((((Γ.lift).insert (.var 0) a).insert
              (PiCalculus.liftName 0 x) b)),
            liftRename g k = liftRename g l → k = l := by
          intro k hk l hl hkl
          have hk' : k = .var 0 ∨ ∃ k₀ ∈ Γ.insert x (.parr a b),
              PiCalculus.liftName 0 k₀ = k := by
            rw [Finmap.mem_insert] at hk
            obtain rfl | hk := hk
            · exact Or.inr ⟨x, hxO, rfl⟩
            · rw [Finmap.mem_insert] at hk
              obtain rfl | hk := hk
              · exact Or.inl rfl
              · obtain ⟨y, hy, heq⟩ := (hmemL Γ _).mp hk
                exact Or.inr ⟨y, hsub y hy, heq⟩
          have hl' : l = .var 0 ∨ ∃ l₀ ∈ Γ.insert x (.parr a b),
              PiCalculus.liftName 0 l₀ = l := by
            rw [Finmap.mem_insert] at hl
            obtain rfl | hl := hl
            · exact Or.inr ⟨x, hxO, rfl⟩
            · rw [Finmap.mem_insert] at hl
              obtain rfl | hl := hl
              · exact Or.inl rfl
              · obtain ⟨y, hy, heq⟩ := (hmemL Γ _).mp hl
                exact Or.inr ⟨y, hsub y hy, heq⟩
          exact hinjL g _ hg k hk' l hl' hkl
        have hp' : HasType (((Γ'.lift).insert (.var 0) a).insert
            (PiCalculus.liftName 0 (g x)) b)
            (p.rename (liftRename g)) :=
          ihp (liftRename g) hgP _ hIns1
        rw [heq]
        exact HasType.parr hp' hxG'
    | @oplusLeft Γ x a b p hp hxΓ ihp =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x (.oplus a b) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x (.oplus a b) := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) (.oplus a b)).entries =
            ((Γ.insert x (.oplus a b))).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x (.oplus a b) hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) (.oplus a b) := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hsubP : ∀ k ∈ Γ.insert x a, k ∈ Γ.insert x (.oplus a b) := by
          intro k hk
          rw [Finmap.mem_insert] at hk ⊢
          exact hk
        have hgP : ∀ k ∈ Γ.insert x a, ∀ l ∈ Γ.insert x a,
            g k = g l → k = l := fun k hk l hl hkl =>
          hg k (hsubP k hk) l (hsubP l hl) hkl
        have hP' : (Γ'.insert (g x) a).entries =
            ((Γ.insert x a)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x a hΓ' hxΓ hxG'
        have hp' : HasType (Γ'.insert (g x) a) (p.rename g) :=
          ihp g hgP _ hP'
        rw [heq]
        exact HasType.oplusLeft hp' hxG'
    | @oplusRight Γ x a b p hp hxΓ ihp =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x (.oplus a b) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x (.oplus a b) := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) (.oplus a b)).entries =
            ((Γ.insert x (.oplus a b))).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x (.oplus a b) hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) (.oplus a b) := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hsubP : ∀ k ∈ Γ.insert x b, k ∈ Γ.insert x (.oplus a b) := by
          intro k hk
          rw [Finmap.mem_insert] at hk ⊢
          exact hk
        have hgP : ∀ k ∈ Γ.insert x b, ∀ l ∈ Γ.insert x b,
            g k = g l → k = l := fun k hk l hl hkl =>
          hg k (hsubP k hk) l (hsubP l hl) hkl
        have hP' : (Γ'.insert (g x) b).entries =
            ((Γ.insert x b)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x b hΓ' hxΓ hxG'
        have hp' : HasType (Γ'.insert (g x) b) (p.rename g) :=
          ihp g hgP _ hP'
        rw [heq]
        exact HasType.oplusRight hp' hxG'
    | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x (.with a b) :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x (.with a b) := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) (.with a b)).entries =
            ((Γ.insert x (.with a b))).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x (.with a b) hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) (.with a b) := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hsubC : ∀ (c : Logic.CLL.Proposition Atom) (k : PiCalculus.Name),
            k ∈ Γ.insert x c → k ∈ Γ.insert x (.with a b) := by
          intro c k hk
          rw [Finmap.mem_insert] at hk ⊢
          exact hk
        have hgC : ∀ (c : Logic.CLL.Proposition Atom) (k : PiCalculus.Name),
            k ∈ Γ.insert x c → ∀ (l : PiCalculus.Name), l ∈ Γ.insert x c →
            g k = g l → k = l := fun c k hk l hl hkl =>
          hg k (hsubC c k hk) l (hsubC c l hl) hkl
        have hPa' : (Γ'.insert (g x) a).entries =
            ((Γ.insert x a)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x a hΓ' hxΓ hxG'
        have hPb' : (Γ'.insert (g x) b).entries =
            ((Γ.insert x b)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x b hΓ' hxΓ hxG'
        have hp' : HasType (Γ'.insert (g x) a) (p.rename g) :=
          ihp g (hgC a) _ hPa'
        have hq' : HasType (Γ'.insert (g x) b) (q.rename g) :=
          ihq g (hgC b) _ hPb'
        rw [heq]
        exact HasType.with hp' hq' hxG'
    | @one x =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ (∅ : Context Atom).insert x .one :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hgE : ∀ x ∈ (∅ : Context Atom), ∀ y ∈ (∅ : Context Atom), g x = g y → x = y := by
          intro x hx y hy hxy
          exact (Finmap.notMem_empty hx).elim
        obtain ⟨E', hE'⟩ := hmk g (∅ : Context Atom) hgE
        have hxE' : g x ∉ E' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g ∅ E' hE' _).mp h
          have hyO : y ∈ (∅ : Context Atom).insert x .one :=
            (Finmap.notMem_empty hy).elim
          have heqy : y = x := hg y hyO x hxO heq
          subst heqy
          exact Finmap.notMem_empty hy
        have hO' : (E'.insert (g x) .one).entries =
            (((∅ : Context Atom).insert x .one)).entries.map
              (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g ∅ E' x .one hE' Finmap.notMem_empty hxE'
        have hE'empty : E' = ∅ := by
          apply Finmap.ext
          rw [hE']
          rfl
        rw [hE'empty] at hO'
        have heq : Δ' = (∅ : Context Atom).insert (g x) .one := by
          apply Finmap.ext
          rw [hΔ', hO']
        rw [heq]
        exact HasType.one
    | @bot Γ x p hp hxΓ ihp =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x .bot :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x .bot := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) .bot).entries =
            ((Γ.insert x .bot)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x .bot hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) .bot := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        have hp' : HasType Γ' (p.rename g) :=
          ihp g hgΓ _ hΓ'
        rw [heq]
        exact HasType.bot hp' hxG'
    | @top Γ x hxΓ =>
        intro g hg Δ' hΔ'
        have hxO : x ∈ Γ.insert x .top :=
          Finmap.mem_insert.2 (Or.inl rfl)
        have hsub : ∀ k ∈ Γ, k ∈ Γ.insert x .top := fun k hk =>
          Finmap.mem_insert.2 (Or.inr hk)
        have hgΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, g x = g y → x = y := fun x hx y hy hxy =>
          hg x (hsub x hx) y (hsub y hy) hxy
        obtain ⟨Γ', hΓ'⟩ := hmk g Γ hgΓ
        have hxG' : g x ∉ Γ' := by
          intro h
          obtain ⟨y, hy, heq⟩ := (hmemI g Γ Γ' hΓ' _).mp h
          have heqy : y = x := hg y (hsub y hy) x hxO heq
          subst heqy
          exact hxΓ hy
        have hOuter : (Γ'.insert (g x) .top).entries =
            ((Γ.insert x .top)).entries.map (fun e => ⟨g e.1, e.2⟩) :=
          himgIns g Γ Γ' x .top hΓ' hxΓ hxG'
        have heq : Δ' = Γ'.insert (g x) .top := by
          apply Finmap.ext
          rw [hΔ', hOuter]
        rw [heq]
        exact HasType.top hxG'
  have hls : ∀ (n : PiCalculus.Name) (c : ℕ),
      liftRename (PiCalculus.substName n c) =
        PiCalculus.substName (PiCalculus.liftName 0 n) (c + 1) := by
    intro n c
    funext x
    rcases x with m | _ | i
    · simp only [liftRename, PiCalculus.substName, PiCalculus.liftName]
    · simp only [liftRename, PiCalculus.substName, Nat.zero_lt_succ,
        ↓reduceIte]
    · simp only [liftRename, PiCalculus.substName]
      by_cases h₁ : i < c
      · have h₃ : i + 1 < c + 1 := by omega
        simp only [h₁, h₃, PiCalculus.liftName, Nat.zero_le, ↓reduceIte]
      · by_cases h₂ : i = c
        · subst h₂
          simp only [Nat.lt_irrefl, ↓reduceIte]
        · have h₃ : ¬ i + 1 < c + 1 := by omega
          have h₄ : ¬ i + 1 = c + 1 := by omega
          simp only [h₁, h₂, h₃, h₄, ↓reduceIte, PiCalculus.liftName,
            Nat.zero_le, PiCalculus.Name.var.injEq]
          omega
  have hsr : ∀ (r : Proc Atom) (n : PiCalculus.Name) (c : ℕ),
      r.substAt n c = r.rename (PiCalculus.substName n c) := by
    intro r
    induction r with
    | link x y =>
        intro n c
        rfl
    | cut a p q ihp ihq =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp, ihq, hls]
    | output x p q ihp ihq =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp, ihq, hls]
    | input x p ihp =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp, hls]
    | selectLeft x p ihp =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp]
    | selectRight x p ihp =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp]
    | choice x p q ihp ihq =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp, ihq]
    | emptyOutput x =>
        intro n c
        rfl
    | emptyInput x p ihp =>
        intro n c
        simp only [Proc.substAt, Proc.rename, ihp]
    | emptyChoice x =>
        intro n c
        rfl
  have hsl : ∀ x : PiCalculus.Name,
      PiCalculus.substName w 0 (PiCalculus.liftName 0 x) = x := by
    intro x
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, PiCalculus.substName]
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
          PiCalculus.substName, Nat.not_lt_zero, Nat.add_one_ne_zero,
          Nat.add_sub_cancel]
  have hs0 : PiCalculus.substName w 0 (.var 0) = w := by
    simp only [PiCalculus.substName, Nat.lt_irrefl, ↓reduceIte]
  rw [Proc.subst, hsr]
  refine key hp (PiCalculus.substName w 0) ?_ _ ?_
  · intro x hx y hy hxy
    rw [Finmap.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · obtain ⟨x₀, hx₀, rfl⟩ := (hmemL Γ _).mp hy
        rw [hs0, hsl] at hxy
        rw [← hxy] at hx₀
        exact absurd hx₀ hw
    · rcases hy with rfl | hy
      · obtain ⟨x₀, hx₀, rfl⟩ := (hmemL Γ _).mp hx
        rw [hs0, hsl] at hxy
        rw [hxy] at hx₀
        exact absurd hx₀ hw
      · obtain ⟨x₀, hx₀, rfl⟩ := (hmemL Γ _).mp hx
        obtain ⟨y₀, hy₀, rfl⟩ := (hmemL Γ _).mp hy
        rw [hsl, hsl] at hxy
        rw [hxy]
  · rw [Finmap.entries_insert_of_notMem hw,
      Finmap.entries_insert_of_notMem (hvar0 Γ), Multiset.map_cons]
    simp only [Context.lift, Context.mapKeys, Multiset.map_map,
      Function.comp_def, hsl, hs0, Sigma.eta, Multiset.map_id']

/-- Every syntactically free channel of a typed process occurs in its
environment. The converse does not hold because the `⊤` rule admits an
arbitrary additional environment, exactly as in Figure 1. -/
theorem HasType.freeNames_subset_keys {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) : p.freeNames ⊆ Γ.keys := by
  have hl0ne : ∀ x : PiCalculus.Name, PiCalculus.liftName 0 x ≠ .var 0 := by
    intro x hx
    cases x with
    | const n =>
        simp only [PiCalculus.liftName, reduceCtorEq] at hx
    | var i =>
        simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
          PiCalculus.Name.var.injEq, Nat.add_eq_zero_iff, one_ne_zero,
          and_false] at hx
  have hinj : Function.Injective (PiCalculus.liftName 0) := by
    intro x y hxy
    cases x <;> cases y <;>
      simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, reduceCtorEq,
        PiCalculus.Name.const.injEq, PiCalculus.Name.var.injEq,
        Nat.add_right_cancel_iff] at hxy ⊢ <;>
      exact hxy
  have hback : ∀ (Δ : Context Atom) (a : Logic.CLL.Proposition Atom)
      (y : PiCalculus.Name),
      PiCalculus.liftName 0 y ∈ (Δ.lift).insert (.var 0) a → y ∈ Δ := by
    intro Δ a y hy
    rw [Finmap.mem_insert] at hy
    rcases hy with hy | hy
    · exact (hl0ne y hy).elim
    · rw [Finmap.mem_def] at hy
      simp only [Context.lift, Context.mapKeys, Multiset.keys,
        Multiset.map_map, Function.comp_def, Multiset.mem_map] at hy
      obtain ⟨e, he, hey⟩ := hy
      rw [← hinj hey]
      exact Finmap.mem_def.2 (Multiset.mem_map_of_mem Sigma.fst he)
  have hzero : ∀ z : PiCalculus.Name, freeNameAt 0 z = {z} := by
    intro z
    cases z with
    | const n => rfl
    | var i =>
        simp only [freeNameAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  have hname : ∀ (d : ℕ) (x y : PiCalculus.Name),
      y ∈ freeNameAt (d + 1) x →
      PiCalculus.liftName 0 y ∈ freeNameAt d x := by
    intro d x y hy
    cases x with
    | const n =>
        simp only [freeNameAt, Finset.mem_singleton] at hy ⊢
        subst hy
        rfl
    | var i =>
        simp only [freeNameAt] at hy ⊢
        split_ifs at hy with h₁
        · simp only [Finset.notMem_empty] at hy
        · rw [Finset.mem_singleton] at hy
          subst hy
          have h₂ : ¬ i < d := by omega
          simp only [h₂, ↓reduceIte, Finset.mem_singleton]
          simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
            PiCalculus.Name.var.injEq]
          omega
  have hshift : ∀ (q : Proc Atom) (d : ℕ) (y : PiCalculus.Name),
      y ∈ q.freeNamesAt (d + 1) → PiCalculus.liftName 0 y ∈ q.freeNamesAt d := by
    intro q
    induction q with
    | link x y =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (hname _ _ _ h)
        · exact Or.inr (hname _ _ _ h)
    | cut a p q ihp ihq =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (ihp _ _ h)
        · exact Or.inr (ihq _ _ h)
    | output x p q ihp ihq =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with (h | h) | h
        · exact Or.inl (Or.inl (hname _ _ _ h))
        · exact Or.inl (Or.inr (ihp _ _ h))
        · exact Or.inr (ihq _ _ h)
    | input x p ihp =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (hname _ _ _ h)
        · exact Or.inr (ihp _ _ h)
    | selectLeft x p ihp =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (hname _ _ _ h)
        · exact Or.inr (ihp _ _ h)
    | selectRight x p ihp =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (hname _ _ _ h)
        · exact Or.inr (ihp _ _ h)
    | choice x p q ihp ihq =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with (h | h) | h
        · exact Or.inl (Or.inl (hname _ _ _ h))
        · exact Or.inl (Or.inr (ihp _ _ h))
        · exact Or.inr (ihq _ _ h)
    | emptyOutput x =>
        intro d z hz
        exact hname _ _ _ hz
    | emptyInput x p ihp =>
        intro d z hz
        simp only [Proc.freeNamesAt, Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · exact Or.inl (hname _ _ _ h)
        · exact Or.inr (ihp _ _ h)
    | emptyChoice x =>
        intro d z hz
        exact hname _ _ _ hz
  induction h with
  | @ax w x a hwx =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      simp only [Finmap.mem_insert]
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  | @cut Γ Δ a p q hp hq hdisj ihp ihq =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union] at hy
      rw [Finmap.mem_union]
      rcases hy with h | h
      · exact Or.inl (hback _ _ _ (Finmap.mem_keys.1 (ihp (hshift _ _ _ h))))
      · exact Or.inr (hback _ _ _ (Finmap.mem_keys.1 (ihq (hshift _ _ _ h))))
  | @tensor Γ Δ x a b p q hp hq hdisj hxΓ hxΔ ihp ihq =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      simp only [Finmap.mem_insert, Finmap.mem_union]
      rcases hy with (rfl | h) | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hback _ _ _ (Finmap.mem_keys.1 (ihp (hshift _ _ _ h)))))
      · rcases Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihq h)) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
  | @parr Γ x a b p hp hxΓ ihp =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      rcases hy with rfl | h
      · exact Or.inl rfl
      · rcases Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihp (hshift _ _ _ h))) with h' | h'
        · exact Or.inl (hinj h')
        · exact Or.inr (hback _ _ _ h')
  | @oplusLeft Γ x a b p hp hxΓ ihp =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      rcases hy with rfl | h
      · exact Or.inl rfl
      · exact Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihp h))
  | @oplusRight Γ x a b p hp hxΓ ihp =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      rcases hy with rfl | h
      · exact Or.inl rfl
      · exact Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihp h))
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      rcases hy with (rfl | h) | h
      · exact Or.inl rfl
      · exact Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihp h))
      · exact Finmap.mem_insert.1 (Finmap.mem_keys.1 (ihq h))
  | @one x =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      exact Or.inl hy
  | @bot Γ x p hp hxΓ ihp =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero, Finset.mem_union,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      rcases hy with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Finmap.mem_keys.1 (ihp h))
  | @top Γ x hxΓ =>
      intro y hy
      rw [Finmap.mem_keys]
      simp only [Proc.freeNames, Proc.freeNamesAt, hzero,
        Finset.mem_singleton] at hy
      rw [Finmap.mem_insert]
      exact Or.inl hy

end Cslib.ClassicalProcesses
