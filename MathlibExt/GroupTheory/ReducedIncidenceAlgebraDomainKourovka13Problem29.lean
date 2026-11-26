/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Finset.Powerset
public import Mathlib.GroupTheory.GroupAction.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# The invariant reduced incidence algebra is a domain (Kourovka Notebook Problem 13.29)

The theorem `invariantIncidenceAlgebraIsDomain_holds` proves Cameron's conjecture that
the invariant algebra has no zero divisors when every point orbit is infinite.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.29 (P. J.
Cameron). UnsolvedMath record UM-00700947 (`KOU-13.29`), dataset ulamai/UnsolvedMath v1.8.0.

Elements of `A` are functions on finite subsets vanishing above some size, and the product `(fg)(X)
= ∑_{Y ⊆ X} f(Y) g(X ∖ Y)` restricts to the problem's product on `Vₙ × Vₘ` and extends it
bilinearly. `A^G` consists of the `G`-invariant elements. Being an integral domain is stated as the
absence of zero divisors in `A^G` (the unit of `V₀` is nonzero). The definitions agree with
`OpenConjectures` entry `Kourovka19Problem18`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted

variable {Ω : Type*} [DecidableEq Ω]

/-- **Product of the reduced incidence algebra.** Let $\Omega$ be a set. For functions $f$ and $g$
from the finite subsets of $\Omega$ to $\mathbb{Q}$, their product $fg$ is the function on finite
subsets given by $(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$.

If $f$ vanishes off the $n$-element subsets and $g$ vanishes off the $m$-element subsets, this is
the product of Kourovka Problem 13.29, and $fg$ vanishes off the $(n+m)$-element subsets. -/
def incMul (f g : Finset Ω → ℚ) : Finset Ω → ℚ :=
  fun X => ∑ Y ∈ X.powerset, f Y * g (X \ Y)

/-- **Elements of the reduced incidence algebra.** Let $\Omega$ be a set. A function $f$ from the
finite subsets of $\Omega$ to $\mathbb{Q}$ lies in the algebra $A = \bigoplus_n V_n$, where $V_n$
consists of the functions vanishing off the $n$-element subsets, when there is a natural number
$N$ such that $f(X) = 0$ for every finite subset $X$ of $\Omega$ with more than $N$ elements. -/
def IsInA (f : Finset Ω → ℚ) : Prop :=
  ∃ N : ℕ, ∀ X : Finset Ω, N < X.card → f X = 0

/-- **Invariant functions on finite subsets.** Let $G$ be a group of permutations of a set
$\Omega$. A function $f$ from the finite subsets of $\Omega$ to $\mathbb{Q}$ is $G$-invariant when
$f(\sigma(X)) = f(X)$ for every $\sigma \in G$ and every finite subset $X$ of $\Omega$, where
$\sigma(X)$ is the image of $X$ under $\sigma$. -/
def IsInvariant (G : Subgroup (Equiv.Perm Ω)) (f : Finset Ω → ℚ) : Prop :=
  ∀ σ ∈ G, ∀ X : Finset Ω, f (X.map σ.toEmbedding) = f X

/-- **Cameron's conjecture on invariant incidence algebras (Kourovka 13.29).** The statement that
for every infinite set $\Omega$ and every group $G$ of permutations of $\Omega$ all of whose orbits
are infinite, the following holds: if $f$ and $g$ are nonzero functions from the finite subsets of
$\Omega$ to $\mathbb{Q}$ that are $G$-invariant ($f(\sigma(X)) = f(X)$ for all $\sigma \in G$ and
all finite $X$, and likewise for $g$) and that each vanish on all subsets of size larger than some
bound, then their product $fg$ in the reduced incidence algebra, given by
$(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$, is not identically zero. In other words,
the algebra $A^G$ of $G$-invariant elements of the reduced incidence algebra $A$ has no zero
divisors. -/
def invariantIncidenceAlgebraIsDomain : Prop :=
  ∀ (Ω : Type) [DecidableEq Ω] [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)),
    (∀ x : Ω, (MulAction.orbit G x).Infinite) →
    ∀ f g : Finset Ω → ℚ, IsInA f → IsInvariant G f → IsInA g → IsInvariant G g →
      f ≠ 0 → g ≠ 0 → incMul f g ≠ 0

/-! ## The set algebra modulo finite transversals

Work in the full set algebra, allowing unbounded degree. Two functions represent the same class
if they agree on all subsets disjoint from some finite set. For a finite set `D`, taking the
coefficient at `D` means fixing those elements and varying the subset outside `D`. The product
rule splits `D` between the two factors.

If two nonzero classes annihilate each other, this rule forces each to be nilpotent.
For a bounded-degree function, take its first vanishing power and a minimal nonempty face
with nonzero coefficient away from a finite transversal for that power. The product rule
reduces to the linear term of the power on this face. Its coefficient has smaller degree,
so induction rules out the annihilation. Finally, Neumann's coset-cover lemma moves any
finite witness away from any proposed finite transversal. -/

private def Series (α : Type*) := Finset α → ℚ

private instance seriesZero : Zero (Series Ω) := ⟨fun _ => 0⟩
private instance seriesAdd : Add (Series Ω) := ⟨fun f g X => f X + g X⟩
private instance seriesNeg : Neg (Series Ω) := ⟨fun f X => -f X⟩
private instance seriesOne : One (Series Ω) := ⟨fun X => if X = ∅ then 1 else 0⟩
private instance seriesMul : Mul (Series Ω) := ⟨incMul⟩

private lemma conv_assoc (f g h : Series Ω) :
    incMul (incMul f g) h = incMul f (incMul g h) := by
  funext X
  simp only [incMul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.2, p.1 \ p.2⟩) (fun p => ⟨p.1 ∪ p.2, p.1⟩)
  all_goals
    simp only [Finset.mem_sigma, Finset.mem_powerset, and_imp, Sigma.forall, Sigma.mk.inj_iff]
  · intro a b ha hb
    exact ⟨hb.trans ha, Finset.sdiff_subset_sdiff ha Finset.Subset.rfl⟩
  · intro a b ha hb
    exact ⟨Finset.union_subset ha (hb.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro a b ha hb
    simp [Finset.union_sdiff_of_subset hb]
  · intro a b ha hb
    have hd : Disjoint b a := Finset.disjoint_of_subset_left hb disjoint_sdiff_self_left
    simp [Finset.union_sdiff_cancel_left hd.symm]
  · intro a b ha hb
    have he : (X \ b) \ (a \ b) = X \ a := by
      ext x
      simp only [Finset.mem_sdiff]
      grind
    simp [he, mul_assoc]

private lemma conv_comm (f g : Series Ω) : incMul f g = incMul g f := by
  funext X
  unfold incMul
  apply Finset.sum_nbij' (X \ ·) (X \ ·) <;> simp +contextual [mul_comm]

private noncomputable instance seriesRing : CommRing (Series Ω) :=
  CommRing.ofMinimalAxioms (fun _ _ _ => funext fun _ => add_assoc ..)
    (fun _ => funext fun _ => zero_add _) (fun _ => funext fun _ => neg_add_cancel _)
    conv_assoc conv_comm (fun f => by
      funext X
      change (∑ Y ∈ X.powerset, (if Y = ∅ then (1 : ℚ) else 0) * f (X \ Y)) = f X
      simp [ite_mul]) (fun f g h => by
      funext X
      change (∑ Y ∈ X.powerset, f Y * (g (X \ Y) + h (X \ Y))) =
        incMul f g X + incMul f h X
      simp [incMul, mul_add, Finset.sum_add_distrib])

/-- Functions whose support has a finite transversal form an ideal. -/
private def covered : Ideal (Series Ω) where
  carrier := {f | ∃ S : Finset Ω, ∀ X, Disjoint X S → f X = 0}
  zero_mem' := ⟨∅, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S, hS⟩ ⟨T, hT⟩
    exact ⟨S ∪ T, fun X h => by
      change f X + g X = 0
      rw [hS _ (h.mono_right Finset.subset_union_left),
        hT _ (h.mono_right Finset.subset_union_right), add_zero]⟩
  smul_mem' := by
    rintro f g ⟨S, hS⟩
    exact ⟨S, fun X h => Finset.sum_eq_zero fun Y _ => by
      rw [hS _ (h.mono_left Finset.sdiff_subset), mul_zero]⟩

private abbrev Germ (Ω : Type*) [DecidableEq Ω] := Series Ω ⧸ (covered : Ideal (Series Ω))

private noncomputable abbrev germ : Series Ω →+* Germ Ω := Ideal.Quotient.mk covered

private lemma germ_zero (f : Series Ω) : germ f = 0 ↔
    ∃ S : Finset Ω, ∀ X, Disjoint X S → f X = 0 := Ideal.Quotient.eq_zero_iff_mem

private def face (f : Series Ω) (D : Finset Ω) : Series Ω :=
  fun X => if Disjoint X D then f (D ∪ X) else 0

private noncomputable def coeff (f : Series Ω) (D : Finset Ω) : Germ Ω := germ (face f D)

private lemma coeff_empty (f : Series Ω) : coeff f ∅ = germ f := by
  apply congrArg germ
  funext X
  simp [face]

private lemma coeff_vanish {h : Series Ω} {S D : Finset Ω}
    (hh : ∀ X, Disjoint X S → h X = 0) (hd : Disjoint D S) : coeff h D = 0 := by
  apply (germ_zero _).2
  exact ⟨S, fun X hX => by simp [face, hh _ (Finset.disjoint_union_left.mpr ⟨hd, hX⟩)]⟩

private lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → Series Ω) (X : Finset Ω) :
    (∑ i ∈ s, f i) X = ∑ i ∈ s, f i X := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact congrArg (f i X + ·) ih

private lemma coeff_mul (f g : Series Ω) (D : Finset Ω) :
    coeff (f * g) D = ∑ C ∈ D.powerset, coeff f C * coeff g (D \ C) := by
  simp only [coeff, ← map_mul, ← map_sum]
  rw [← sub_eq_zero, ← map_sub, germ_zero]
  refine ⟨D, fun X hX => ?_⟩
  rw [sub_eq_add_neg]
  change face (f * g) D X + - (∑ C ∈ D.powerset, face f C * face g (D \ C)) X = 0
  rw [← sub_eq_add_neg, sub_eq_zero, sum_apply]
  simp only [face, ite_eq_left hX]
  change incMul f g (D ∪ X) = ∑ C ∈ D.powerset, incMul (face f C) (face g (D \ C)) X
  simp only [incMul]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun U => (U ∩ D, U ∩ X)) (fun p => p.1 ∪ p.2)
  all_goals simp only [Finset.mem_product, Finset.mem_powerset, Prod.forall, and_imp]
  · exact fun _ _ => ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · exact fun _ _ ha hb => Finset.union_subset_union ha hb
  · intro U hU
    ext i
    simp only [Finset.mem_union, Finset.mem_inter] at *
    grind
  · intro U V hU hV
    apply Prod.ext <;> dsimp <;> ext i <;>
      simp only [Finset.mem_inter, Finset.mem_union] <;>
      grind [Finset.disjoint_left]
  · intro U hU
    have h₁ : Disjoint (U ∩ X) (U ∩ D) :=
      (hX.mono_left Finset.inter_subset_right).mono_right Finset.inter_subset_right
    have h₂ : Disjoint (X \ (U ∩ X)) (D \ (U ∩ D)) :=
      (hX.mono_left Finset.sdiff_subset).mono_right Finset.sdiff_subset
    simp only [face, ite_eq_left h₁, ite_eq_left h₂]
    congr 2 <;> ext i <;> simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] <;>
      grind

/-- A nonzero constant coefficient allows cancellation, even after a finite deletion. -/
private lemma regular_const {g h : Series Ω} (hg : g ∅ ≠ 0) (hz : germ h * germ g = 0) :
    germ h = 0 := by
  rw [← map_mul, germ_zero] at hz
  obtain ⟨S, hS⟩ := hz
  refine (germ_zero _).2 ⟨S, fun X => ?_⟩
  induction X using Finset.strongInductionOn with
  | _ X ih =>
    intro hX
    have he : incMul h g X = h X * g ∅ := by
      unfold incMul
      rw [Finset.sum_eq_single X]
      · simp
      · intro Y hY hn
        rw [ih Y (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hY, hn⟩)
          (hX.mono_left (Finset.mem_powerset.mp hY)), zero_mul]
      · simp
    exact (mul_eq_zero.mp (he.symm.trans (hS X hX))).resolve_right hg

/-- Multiplying the coefficient equation at each face by a power kills all its proper-face
terms. Thus an annihilator of a function surviving finite deletion is nilpotent in the quotient. -/
private lemma nilpotent_of_annihilator {f g : Series Ω} (hg : germ g ≠ 0)
    (hz : germ f * germ g = 0) : IsNilpotent (germ f) := by
  rw [← map_mul, germ_zero] at hz
  obtain ⟨S, hS⟩ := hz
  have hex : ∃ B, Disjoint B S ∧ g B ≠ 0 := by
    by_contra! hn
    exact hg ((germ_zero _).2 ⟨S, hn⟩)
  obtain ⟨B, hB, hgB⟩ := hex
  have vanish (C : Finset Ω) : C ⊆ B → ∀ n, C.card < n →
      germ f ^ n * coeff g C = 0 := by
    induction C using Finset.strongInductionOn with
    | _ C ih =>
      intro hC n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have he := coeff_vanish hS (hB.mono_left hC)
      rw [coeff_mul, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset C),
        coeff_empty, Finset.sdiff_empty] at he
      have he' := congrArg (germ f ^ m * ·) he
      rw [mul_add, Finset.mul_sum, mul_zero] at he'
      have hz' : ∑ A ∈ C.powerset.erase ∅, germ f ^ m * (coeff f A * coeff g (C \ A)) = 0 := by
        apply Finset.sum_eq_zero
        intro A hA
        obtain ⟨hne, ha⟩ := Finset.mem_erase.mp hA
        have hlt := Finset.sdiff_ssubset (Finset.mem_powerset.mp ha)
          (Finset.nonempty_iff_ne_empty.mpr hne)
        rw [mul_left_comm, ih _ hlt (Finset.sdiff_subset.trans hC) m (by
          have := Finset.card_lt_card hlt
          omega), mul_zero]
      rwa [hz', add_zero, ← mul_assoc, ← pow_succ] at he'
  refine ⟨B.card + 1, ?_⟩
  rw [← map_pow]
  apply regular_const (g := face g B) (by simpa [face] using hgB)
  simpa only [map_pow, coeff] using vanish B Finset.Subset.rfl (B.card + 1) (by omega)

/-- On a minimal nonempty face the product rule for a power has just its linear term. -/
private lemma coeff_pow {f : Series Ω} {D : Finset Ω} (hd : D.Nonempty)
    (hm : ∀ C ⊂ D, C.Nonempty → coeff f C = 0) (k : ℕ) :
    coeff (f ^ (k + 1)) D = (k + 1 : ℕ) * germ f ^ k * coeff f D := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' f (k + 1), coeff_mul, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset D),
      coeff_empty, Finset.sdiff_empty, ih, Finset.sum_eq_single D]
    · rw [Finset.sdiff_self, coeff_empty, map_pow]
      push_cast
      ring
    · intro C hC hne
      obtain ⟨hn, hsub⟩ := Finset.mem_erase.mp hC
      rw [hm C (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hsub, hne⟩)
        (Finset.nonempty_iff_ne_empty.mpr hn), zero_mul]
    · simp [hd.ne_empty]

private lemma cast_empty (n : ℕ) : (n : Series Ω) ∅ = (n : ℚ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ]
    change (n : Series Ω) ∅ + 1 = _
    simp [ih]

/-- For bounded degree, every zero divisor modulo finite transversals already vanishes
modulo finite transversals. -/
private lemma covered_of_zero_product (d : ℕ) (f h : Series Ω)
    (hf : ∀ X, d < X.card → f X = 0) (hh : germ h ≠ 0) (hz : germ f * germ h = 0) :
    germ f = 0 := by
  classical
  induction d using Nat.strong_induction_on generalizing f h with
  | ind d ih =>
    by_contra hne
    have : Nontrivial (Germ Ω) := nontrivial_of_ne _ _ hh
    have hn := nilpotent_of_annihilator hh hz
    obtain ⟨k, hk, hprev⟩ : ∃ k : ℕ, germ f ^ (k + 1) = 0 ∧ germ f ^ k ≠ 0 := by
      let n := Nat.find hn
      have hzero : germ f ^ n = 0 := Nat.find_spec hn
      obtain ⟨k, heq⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by
        intro heq
        simp [heq] at hzero)
      exact ⟨k, by rwa [heq] at hzero, Nat.find_min hn (show k < n by omega)⟩
    rw [← map_pow, germ_zero] at hk
    obtain ⟨S, hS⟩ := hk
    have hB : ∃ B, Disjoint B S ∧ f B ≠ 0 := by
      by_contra! hall
      exact hne ((germ_zero _).2 ⟨S, hall⟩)
    obtain ⟨B, hBS, hfB⟩ := hB
    have hb : B.Nonempty := by
      by_contra! hempty
      subst B
      exact hh (regular_const hfB (mul_comm (germ h) _ ▸ hz))
    let faces := B.powerset.filter (fun C => C.Nonempty ∧ coeff f C ≠ 0)
    have hmem : B ∈ faces := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, hb, ?_⟩
      intro hzB
      obtain ⟨T, hT⟩ := (germ_zero _).1 hzB
      exact hfB (by simpa [face] using hT ∅ (by simp))
    obtain ⟨D, hD, hmin⟩ := faces.exists_min_image Finset.card ⟨B, hmem⟩
    obtain ⟨hDB, hd, hDne⟩ := Finset.mem_filter.mp hD
    have hminimal (C : Finset Ω) (hlt : C ⊂ D) (hc : C.Nonempty) : coeff f C = 0 := by
      by_contra hC
      have := hmin C (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (hlt.subset.trans (Finset.mem_powerset.mp hDB)), hc, hC⟩)
      exact (Finset.card_lt_card hlt).not_ge this
    have he := coeff_vanish hS (hBS.mono_left (Finset.mem_powerset.mp hDB))
    rw [coeff_pow hd hminimal] at he
    have hc : germ (f ^ k * face f D) = 0 := by
      apply regular_const (g := (k + 1 : ℕ))
      · rw [cast_empty]
        positivity
      · rw [map_mul, map_pow, map_natCast]
        change germ f ^ k * coeff f D * _ = 0
        convert he using 1
        ring
    have hdeg : 0 < d := by
      by_contra! h
      exact hfB (hf B (by have := Finset.card_pos.mpr hb; omega))
    apply hDne
    apply ih (d - 1) (by omega) (face f D) (f ^ k) _ (by simpa using hprev)
    · rwa [map_mul, mul_comm] at hc
    · intro X hX
      by_cases hx : Disjoint X D
      · simp only [face, ite_eq_left hx]
        apply hf
        rw [Finset.card_union_of_disjoint hx.symm]
        have := Finset.card_pos.mpr hd
        omega
      · simp [face, hx]

open scoped Pointwise in
omit [DecidableEq Ω] in
private lemma exists_avoiding (G : Subgroup (Equiv.Perm Ω))
    (ho : ∀ x : Ω, (MulAction.orbit G x).Infinite) (X S : Finset Ω) :
    ∃ σ : G, Disjoint (X.map σ.val.toEmbedding) S := by
  classical
  by_contra! h
  let rep (p : Ω × Ω) : G :=
    if he : ∃ σ : G, σ • p.1 = p.2 then he.choose else 1
  have hc : ⋃ p ∈ X ×ˢ S, rep p • (MulAction.stabilizer G p.1 : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro σ
    obtain ⟨y, hy, hS⟩ := Finset.not_disjoint_iff.mp (h σ)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    let p : Ω × Ω := (x, σ • x)
    have he : ∃ τ : G, τ • p.1 = p.2 := ⟨σ, rfl⟩
    have hr : rep p • x = σ • x := by
      dsimp only [rep]
      rw [dite_eq_left he]
      exact he.choose_spec
    refine Set.mem_iUnion₂.mpr ⟨p, Finset.mem_product.mpr ⟨hx, hS⟩, ?_⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
      inv_smul_eq_iff]
    exact hr.symm
  obtain ⟨p, _, hp⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hc
  exact hp.index_ne_zero ((MulAction.index_stabilizer G p.1).trans (ho p.1).ncard)

private lemma germ_ne_of_invariant (G : Subgroup (Equiv.Perm Ω))
    (ho : ∀ x : Ω, (MulAction.orbit G x).Infinite) {f : Finset Ω → ℚ}
    (hi : IsInvariant G f) (hf : f ≠ 0) : germ (Ω := Ω) f ≠ 0 := by
  intro hz
  obtain ⟨S, hS⟩ := (germ_zero _).1 hz
  apply hf
  funext X
  obtain ⟨σ, hd⟩ := exists_avoiding G ho X S
  exact (hi σ σ.property X).symm.trans (hS _ hd)

private lemma germ_mul_eq_zero {f g : Series Ω} (hz : incMul f g = 0) :
    germ f * germ g = 0 := by
  rw [← map_mul]
  exact (congrArg germ (show f * g = 0 from hz)).trans germ.map_zero'

/--
**Cameron's conjecture on invariant incidence algebras holds (Pouzet).** Let $\Omega$ be an
infinite set and let $G$ be a group of permutations of $\Omega$ all of whose orbits are infinite.
Let $f$ and $g$ be nonzero functions from the finite subsets of $\Omega$ to $\mathbb{Q}$ that are
$G$-invariant ($f(\sigma(X)) = f(X)$ for all $\sigma \in G$ and all finite $X$, and likewise for
$g$) and that each vanish on all subsets of size larger than some bound. Then their product in the
reduced incidence algebra, $(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$, is not
identically zero. In other words, the algebra $A^G$ of $G$-invariant elements of the reduced
incidence algebra $A$ has no zero divisors.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.29 (P. J. Cameron); resolution: M. Pouzet, Theor. Inform. Appl. 42 (2008), no. 1, 83-103,
Kourovka Archive, Problem 13.29: the conjecture is proved.
-/
theorem invariantIncidenceAlgebraIsDomain_holds : invariantIncidenceAlgebraIsDomain := by
  intro Ω _ _ G ho f g hf hif _ hig hnf hng hz
  obtain ⟨d, hd⟩ := hf
  apply germ_ne_of_invariant G ho hif hnf
  apply covered_of_zero_product d f g hd (germ_ne_of_invariant G ho hig hng)
  exact germ_mul_eq_zero hz

end MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted
