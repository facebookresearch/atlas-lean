/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Rice–Shapiro theorem
-/
module

public import CSLibExt.Computability.Decidability.Totality
public import MathlibExt.Computability.RE

/-!
# The Rice–Shapiro theorem

Let `C` be a class of partial functions `ℕ →. ℕ` whose index set `{c | c.eval ∈ C}` is
recognizable by a multi-stack machine (`FinTM2`). The index set only sees the partial recursive
members of `C`, so both conditions are about partial recursive functions. This file proves the
two necessary conditions of the Rice–Shapiro theorem:

* **Upward closure** (`rice_shapiro_mono`): if `f ∈ C` is partial recursive and the partial
  recursive `g` extends `f`, then `g ∈ C`. Otherwise run `f` in parallel with "if `c` halts on
  `0`, then `g`". This code computes `f` when `c` does not halt and `g` when it does, which
  reduces the complement of halting to the index set.
* **Finite approximation** (`rice_shapiro_finite`): if `f ∈ C` is partial recursive, then some
  partial recursive subfunction of `f` with finite domain is in `C`. Otherwise compute `f` only
  on inputs `x` at which `c` has not halted on `0` within `x` steps. This is `f` when `c` never
  halts, and a finite subfunction of `f` when it does.

Both use the parametrized s-m-n theorem `MetaMathlibExt.exists_computable_code` and the fact that
the complement of halting is not recognizable (`not_tm2CoRecognizable_halting`).

**The effective form** (`tm2Recognizable_iff_exists_basis`). Finite functions are given by lists
`θ : List (ℕ × ℕ)` (`finFun`, the first listed value at each input); `θ` is a graph (`IsGraph`)
when every listed pair agrees with that value, and `θ` is below `f` when `f` takes every listed
value. The index set of `C` is recognizable iff some recognizable set `B` of graphs is a
**basis** of the partial recursive members of `C`: a partial recursive `f` is in `C` iff it is
above some `θ ∈ B`. (Members that are not partial recursive are invisible to the index set, and
no basis needs to describe them.)

* Necessity (`exists_basis_of_tm2Recognizable`): take for `B` the graphs whose finite function is
  in `C`. It is recognizable because being a graph is decidable (`rePred_isGraph`) and through a
  computable code for `finFun θ`. It is a basis by the two conditions above, since every
  finite-domain partial function is a `finFun` of a graph (`exists_finFun_eq`).
* Sufficiency (`tm2Recognizable_of_basis`): `c.eval ∈ C` iff some `θ ∈ B` is below `c.eval`.
  Being below `c.eval` is recognizable for a finite graph (`rePred_subgraph`, a search for a step
  bound of `Nat.Partrec.Code.evaln`), and recognizable relations are closed under `∃`.

## References

* H. G. Rice, *On completely recursively enumerable classes and their key arrays*, J. Symbolic
  Logic 21 (1956), 304–308.
* N. Shapiro, *Degrees of computability*, Trans. Amer. Math. Soc. 82 (1956), 281–299.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability
open Nat.Partrec (Code)

/-- **Rice–Shapiro, upward closure**: in a class with a recognizable index set, every partial
recursive extension of a partial recursive member is a member. -/
theorem rice_shapiro_mono (C : Set (ℕ →. ℕ)) (hC : TM2Recognizable fun c : Code ↦ c.eval ∈ C)
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfC : f ∈ C)
    (hfg : ∀ x, ∀ y ∈ f x, y ∈ g x) : g ∈ C := by
  by_contra hgC
  have hf' : Partrec fun p : Code × ℕ ↦ f p.2 := (Partrec.nat_iff.2 hf).comp Computable.snd
  have hg' : Partrec fun p : Code × ℕ ↦ (p.1.eval 0).bind fun _ ↦ g p.2 :=
    Partrec.bind (Code.eval_part.comp Computable.fst (Computable.const 0))
      ((Partrec.nat_iff.2 hg).comp (Computable.snd.comp Computable.fst))
  obtain ⟨k, hk, hkmem⟩ := Partrec.merge hf' hg' fun p y hy z hz ↦ by
    obtain ⟨_, -, hz⟩ := Part.mem_bind_iff.mp hz
    exact Part.mem_unique (hfg p.2 y hy) hz
  obtain ⟨h, hh, hheval⟩ := MetaMathlibExt.exists_computable_code (F := fun c x ↦ k (c, x)) hk
  have hred : ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) fun c : Code ↦ c.eval ∈ C := by
    refine ⟨h, hh, fun c ↦ ⟨fun hc ↦ ?_, fun hC' hc ↦ hgC ?_⟩⟩
    · have : (h c).eval = f := by
        funext x
        refine Part.ext fun y ↦ ?_
        rw [hheval, hkmem]
        refine ⟨fun H ↦ H.resolve_right fun hy ↦ hc ?_, Or.inl⟩
        obtain ⟨a, ha, -⟩ := Part.mem_bind_iff.mp hy
        exact Part.dom_iff_mem.mpr ⟨a, ha⟩
      simp only [this]
      exact hfC
    · have : (h c).eval = g := by
        funext x
        refine Part.ext fun y ↦ ?_
        rw [hheval, hkmem]
        constructor
        · rintro (hy | hy)
          · exact hfg x y hy
          · obtain ⟨_, -, hy⟩ := Part.mem_bind_iff.mp hy
            exact hy
        · exact fun hy ↦ Or.inr (Part.mem_bind_iff.mpr ⟨_, Part.get_mem hc, hy⟩)
      simpa only [this] using hC'
  exact not_tm2CoRecognizable_halting 0 (tm2Recognizable_of_manyOneReducible hred hC)

/-- **Rice–Shapiro, finite approximation**: every partial recursive member of a class with a
recognizable index set has a partial recursive finite subfunction in the class. -/
theorem rice_shapiro_finite (C : Set (ℕ →. ℕ)) (hC : TM2Recognizable fun c : Code ↦ c.eval ∈ C)
    {f : ℕ →. ℕ} (hf : Nat.Partrec f) (hfC : f ∈ C) :
    ∃ θ : ℕ →. ℕ, Nat.Partrec θ ∧ (∀ x, ∀ y ∈ θ x, y ∈ f x) ∧ θ.Dom.Finite ∧ θ ∈ C := by
  by_contra H
  push Not at H
  have hk : Partrec₂ fun (c : Code) (x : ℕ) ↦
      bif (Code.evaln x c 0).isSome then Part.none else f x :=
    Partrec.cond (Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const 0)))).to_comp Partrec.none
      ((Partrec.nat_iff.2 hf).comp Computable.snd)
  obtain ⟨h, hh, hheval⟩ := MetaMathlibExt.exists_computable_code hk
  have hred : ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) fun c : Code ↦ c.eval ∈ C := by
    refine ⟨h, hh, fun c ↦ ⟨fun hc ↦ ?_, fun hC' hc ↦ ?_⟩⟩
    · have : (h c).eval = f := by
        funext x
        rw [hheval]
        cases he : Code.evaln x c 0 with
        | none => rfl
        | some z => exact absurd (Part.dom_iff_mem.mpr ⟨z, Code.evaln_sound he⟩) hc
      simp only [this]
      exact hfC
    · obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hc
      obtain ⟨s, hs⟩ := Code.evaln_complete.mp hz
      refine H (h c).eval (Code.exists_code.2 ⟨h c, rfl⟩) (fun x y hy ↦ ?_) ?_ hC'
      · rw [hheval] at hy
        revert hy
        cases (Code.evaln x c 0).isSome
        · exact id
        · intro hy
          simp at hy
      · refine (Set.finite_lt_nat s).subset fun x hx ↦ ?_
        by_contra hxs
        have hsx : Code.evaln x c 0 = some z := Code.evaln_mono (Nat.le_of_not_lt hxs) hs
        have hx' : ((h c).eval x).Dom := hx
        simp [hheval, hsx] at hx'
  exact not_tm2CoRecognizable_halting 0 (tm2Recognizable_of_manyOneReducible hred hC)


/-! ### The effective form -/

/-- **Finite function of a list of pairs.** For a finite list $\theta$ of pairs of natural
numbers, the finite function of $\theta$ is the partial function
$\mathbb{N} \rightharpoonup \mathbb{N}$ whose value at $x$ is the second component of the first
pair in $\theta$ with first component $x$, and which is undefined at $x$ when $\theta$ has no pair
with first component $x$. -/
def finFun (θ : List (ℕ × ℕ)) : ℕ →. ℕ := fun x ↦
  ((θ.filterMap fun p ↦ if p.1 = x then some p.2 else none).head? : Part ℕ)

theorem mem_of_mem_finFun {θ : List (ℕ × ℕ)} {x y : ℕ} (h : y ∈ finFun θ x) : (x, y) ∈ θ := by
  have h' : (θ.filterMap fun p ↦ if p.1 = x then some p.2 else none).head? = some y := by
    simpa [finFun] using h
  obtain ⟨p, hp, hpy⟩ := List.mem_filterMap.mp (List.mem_of_mem_head? h')
  split_ifs at hpy with hpx
  cases hpy
  rw [← hpx]
  exact hp

/-- **Graphs of finite functions.** A finite list $\theta$ of pairs of natural numbers is a graph
when, for every pair $(x, y)$ in $\theta$, the finite function of $\theta$ takes the value $y$ at
$x$; that is, the first pair in $\theta$ with first component $x$ is $(x, y)$. -/
def IsGraph (θ : List (ℕ × ℕ)) : Prop := ∀ p ∈ θ, p.2 ∈ finFun θ p.1

/-- **Being a graph is recursively enumerable.** The set of finite lists of pairs of natural
numbers that are graphs is recursively enumerable.

This set is in fact decidable. -/
theorem rePred_isGraph : REPred IsGraph := by
  have hsel : Primrec₂ fun (q : List (ℕ × ℕ) × (ℕ × ℕ)) (r : ℕ × ℕ) ↦
      if r.1 = q.2.1 then some r.2 else none :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  have hdec : PrimrecPred fun q : List (ℕ × ℕ) × (ℕ × ℕ) ↦
      (q.1.filterMap fun r ↦ if r.1 = q.2.1 then some r.2 else none).head? = some q.2.2 :=
    Primrec.eq.comp (Primrec.list_head?.comp (Primrec.listFilterMap Primrec.fst hsel))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  obtain ⟨d, hd⟩ := hdec
  have hR : REPred fun q : List (ℕ × ℕ) × (ℕ × ℕ) ↦ q.2.2 ∈ finFun q.1 q.2.1 :=
    (ComputablePred.to_re ⟨d, hd.to_comp⟩).of_eq fun q ↦ by simp [finFun]
  exact MetaMathlibExt.REPred.forall_mem (c := id) hR Primrec.id

theorem partrec₂_finFun : Partrec₂ fun (θ : List (ℕ × ℕ)) (x : ℕ) ↦ finFun θ x := by
  have hsel : Primrec₂ fun (q : List (ℕ × ℕ) × ℕ) (p : ℕ × ℕ) ↦
      if p.1 = q.2 then some p.2 else none :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  exact (Computable.ofOption (Primrec.list_head?.comp
    (Primrec.listFilterMap Primrec.fst hsel)).to_comp).of_eq fun _ ↦ rfl

theorem nat_partrec_finFun (θ : List (ℕ × ℕ)) : Nat.Partrec (finFun θ) :=
  Partrec.nat_iff.mp (partrec₂_finFun.comp (Computable.const θ) Computable.id)

theorem head?_filterMap_ite (s : List ℕ) (x : ℕ) (F : ℕ → Option ℕ) :
    (s.filterMap fun z ↦ if z = x then F z else none).head? = if x ∈ s then F x else none := by
  induction s with
  | nil => simp
  | cons z s ih =>
    by_cases hz : z = x
    · subst hz
      cases h : F z <;> simp_all
    · simp [hz, ih, Ne.symm hz]

/-- **Finite-domain partial functions are finite functions.** For every partial function
$g : \mathbb{N} \rightharpoonup \mathbb{N}$ with finite domain there is a finite list $\theta$ of
pairs of natural numbers such that the finite function of $\theta$ is $g$ and, for every pair
$(x, y)$ in $\theta$, $g(x)$ is defined and equals $y$. -/
theorem exists_finFun_eq {g : ℕ →. ℕ} (hg : g.Dom.Finite) :
    ∃ θ : List (ℕ × ℕ), finFun θ = g ∧ ∀ p ∈ θ, p.2 ∈ g p.1 := by
  classical
  refine ⟨hg.toFinset.toList.filterMap fun z ↦ (g z).toOption.map (Prod.mk z), ?_, ?_⟩
  · funext x
    have key : ∀ z, ((g z).toOption.map (Prod.mk z)).bind
        (fun p ↦ if p.1 = x then some p.2 else none) = if z = x then (g z).toOption else none := by
      intro z
      cases (g z).toOption <;> by_cases hz : z = x <;> simp [hz]
    simp only [finFun, List.filterMap_filterMap, key]
    rw [head?_filterMap_ite]
    by_cases hx : (g x).Dom
    · have hmem : x ∈ hg.toFinset.toList :=
        Finset.mem_toList.mpr ((Set.Finite.mem_toFinset hg).mpr hx)
      simp only [hmem, ↓reduceIte]
      exact Part.ext fun y ↦ by simp
    · have hmem : x ∉ hg.toFinset.toList :=
        fun h ↦ hx ((Set.Finite.mem_toFinset hg).mp (Finset.mem_toList.mp h))
      simp only [hmem, ↓reduceIte]
      exact (Part.eq_none_iff'.mpr hx).symm
  · intro p hp
    obtain ⟨z, -, hz⟩ := List.mem_filterMap.mp hp
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hz
    exact Part.mem_toOption.mp hy

/-- **Extending a finite list of pairs is recursively enumerable.** The set of pairs
$(c, \theta)$, where $c$ is a code of a partial recursive function and $\theta$ is a finite list of
pairs of natural numbers, such that for every pair $(x, y)$ in $\theta$ the function computed by
$c$ is defined at $x$ with value $y$, is recursively enumerable. -/
theorem rePred_subgraph :
    REPred fun q : Code × List (ℕ × ℕ) ↦ ∀ p ∈ q.2, p.2 ∈ q.1.eval p.1 := by
  have hcomp : ComputablePred fun s : (Code × ℕ × ℕ) × ℕ ↦
      Code.evaln s.2 s.1.1 s.1.2.1 = some s.1.2.2 := by
    obtain ⟨d, h⟩ : PrimrecPred fun s : (Code × ℕ × ℕ) × ℕ ↦
        Code.evaln s.2 s.1.1 s.1.2.1 = some s.1.2.2 :=
      Primrec.eq.comp (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.snd
        (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact ⟨d, h.to_comp⟩
  have hmem : REPred fun r : Code × ℕ × ℕ ↦ r.2.2 ∈ r.1.eval r.2.1 :=
    (MetaMathlibExt.REPred.exists hcomp.to_re).of_eq fun r ↦ by
      rw [Code.evaln_complete]
  have hR : REPred fun s : (Code × List (ℕ × ℕ)) × (ℕ × ℕ) ↦ s.2.2 ∈ s.1.1.eval s.2.1 :=
    Partrec.comp hmem (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
  exact MetaMathlibExt.REPred.forall_mem hR Primrec.snd

/-- **Effective Rice–Shapiro, sufficiency.** Let $C$ be a class of partial functions
$\mathbb{N} \rightharpoonup \mathbb{N}$ and let $B$ be a recognizable set of finite lists of pairs
of natural numbers. Suppose that a partial recursive function $f$ is in $C$ if and only if some
$\theta \in B$ satisfies: for every pair $(x, y)$ in $\theta$, $f(x)$ is defined and equals $y$.
Then the index set of $C$, the set of codes $c$ of partial recursive functions such that the
function computed by $c$ is in $C$, is recognizable. -/
theorem tm2Recognizable_of_basis (C : Set (ℕ →. ℕ)) {B : List (ℕ × ℕ) → Prop}
    (hB : TM2Recognizable B)
    (hC : ∀ f : ℕ →. ℕ, Nat.Partrec f → (f ∈ C ↔ ∃ θ, B θ ∧ ∀ p ∈ θ, p.2 ∈ f p.1)) :
    TM2Recognizable fun c : Code ↦ c.eval ∈ C := by
  rw [tm2Recognizable_iff_rePred] at hB ⊢
  have hB' : REPred fun q : Code × List (ℕ × ℕ) ↦ B q.2 := Partrec.comp hB Computable.snd
  exact (MetaMathlibExt.REPred.exists (R := fun (c : Code) (θ : List (ℕ × ℕ)) ↦
    B θ ∧ ∀ p ∈ θ, p.2 ∈ c.eval p.1) (MetaMathlibExt.REPred.and hB' rePred_subgraph)).of_eq
      fun c ↦ (hC _ (Code.exists_code.mpr ⟨c, rfl⟩)).symm

/-- **Effective Rice–Shapiro, necessity.** Let $C$ be a class of partial functions
$\mathbb{N} \rightharpoonup \mathbb{N}$ whose index set, the set of codes $c$ of partial
recursive functions such that the function computed by $c$ is in $C$, is recognizable. Then there
is a recognizable set $B$ of finite lists of pairs of natural numbers, each of which is a graph,
such that a partial recursive function $f$ is in $C$ if and only if some $\theta \in B$
satisfies: for every pair $(x, y)$ in $\theta$, $f(x)$ is defined and equals $y$. -/
theorem exists_basis_of_tm2Recognizable (C : Set (ℕ →. ℕ))
    (hC : TM2Recognizable fun c : Code ↦ c.eval ∈ C) :
    ∃ B : List (ℕ × ℕ) → Prop, TM2Recognizable B ∧ (∀ θ, B θ → IsGraph θ) ∧
      ∀ f : ℕ →. ℕ, Nat.Partrec f → (f ∈ C ↔ ∃ θ, B θ ∧ ∀ p ∈ θ, p.2 ∈ f p.1) := by
  refine ⟨fun θ ↦ IsGraph θ ∧ finFun θ ∈ C, ?_, fun θ hθ ↦ hθ.1, fun f hf ↦ ⟨fun hfC ↦ ?_, ?_⟩⟩
  · obtain ⟨h, hh, hheval⟩ := MetaMathlibExt.exists_computable_code partrec₂_finFun
    have hCθ : TM2Recognizable fun θ ↦ finFun θ ∈ C := by
      refine tm2Recognizable_of_manyOneReducible ⟨h, hh, fun θ ↦ ?_⟩ hC
      rw [show (h θ).eval = finFun θ from funext (hheval θ)]
    exact tm2Recognizable_iff_rePred.mpr
      (MetaMathlibExt.REPred.and rePred_isGraph (tm2Recognizable_iff_rePred.mp hCθ))
  · obtain ⟨g, -, hgf, hfin, hgC⟩ := rice_shapiro_finite C hC hf hfC
    obtain ⟨θ, rfl, hθ⟩ := exists_finFun_eq hfin
    exact ⟨θ, ⟨hθ, hgC⟩, fun p hp ↦ hgf p.1 p.2 (hθ p hp)⟩
  · rintro ⟨θ, ⟨-, hθC⟩, hθf⟩
    exact rice_shapiro_mono C hC (nat_partrec_finFun θ) hf hθC
      fun x y hy ↦ hθf (x, y) (mem_of_mem_finFun hy)

/-- **The effective Rice–Shapiro theorem**: a class of partial functions has a recognizable index
set iff, among partial recursive functions, its members are exactly the extensions of the finite
functions in some recognizable set of graphs. -/
theorem tm2Recognizable_iff_exists_basis (C : Set (ℕ →. ℕ)) :
    TM2Recognizable (fun c : Code ↦ c.eval ∈ C) ↔
      ∃ B : List (ℕ × ℕ) → Prop, TM2Recognizable B ∧ (∀ θ, B θ → IsGraph θ) ∧
        ∀ f : ℕ →. ℕ, Nat.Partrec f → (f ∈ C ↔ ∃ θ, B θ ∧ ∀ p ∈ θ, p.2 ∈ f p.1) :=
  ⟨exists_basis_of_tm2Recognizable C, fun ⟨_, hB, _, hBC⟩ ↦ tm2Recognizable_of_basis C hB hBC⟩

end Cslib.Decidability
