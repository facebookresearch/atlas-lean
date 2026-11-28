/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

open scoped Pointwise Classical symmDiff

/-! # Amenable groups via the Følner condition

A discrete group `G` is *amenable* when it satisfies the **Følner condition**: for
every finite subset `K ⊆ G` and every `ε > 0` there is a finite nonempty subset
`F ⊆ G` that is *almost invariant* under left translation by the elements of `K`,
i.e. `|s • F ∆ F| / |F| < ε` for every `s ∈ K`.

This is the measure-theory-free characterization of amenability. It is classically
equivalent to the existence of a finitely-additive left-invariant probability
measure (an invariant mean / Banach mean) on `G`; that equivalence is not proved
here. Mathlib's `Mathlib.MeasureTheory.Group.FoelnerFilter` develops a
*measure-theoretic* Følner filter for a group action `MulAction G X` on a measure
space and derives an invariant mean on `Set X` (`IsFoelner.amenable`), but it does
not provide this combinatorial predicate on a discrete group; hence the definition
below.

## References

* Følner, *On groups with full Banach mean value* (1955).
* Tullio Ceccherini-Silberstein and Michel Coornaert, *Cellular Automata and Groups*,
  Springer Monographs in Mathematics, Springer, 2010, Theorem 4.4.7 and Proposition 4.5.1
  (pp. 87–89), and Corollary 4.5.2 (p. 89). We use a finite-set count in place of the invariant
  mean, retaining the reduced-word and right-coset arguments. -/

/-- **Amenable group (Følner condition).** A discrete group $G$ is *amenable* if it satisfies the
Følner condition: for every finite subset $K \subseteq G$ and every real $\varepsilon > 0$ there is
a finite nonempty subset $F \subseteq G$ such that
$|sF \mathbin{\triangle} F| / |F| < \varepsilon$ for every $s \in K$. Here
$sF = \{sf : f \in F\}$ is the left translate of $F$ by $s$, $\triangle$ is symmetric difference
and $|\cdot|$ is cardinality. -/
def IsAmenable (G : Type*) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ F : Finset G, F.Nonempty ∧
      ∀ s ∈ K, (((s • F) ∆ F).card : ℝ) / (F.card : ℝ) < ε

/-- **Finite groups are amenable.** Every finite group is amenable.

The whole group $F = G$ is invariant under left translation, so it is a Følner set whose
symmetric-difference ratio is $0$. -/
theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] : IsAmenable G := by
  letI := Fintype.ofFinite G
  intro K ε hε
  refine ⟨Finset.univ, ⟨1, Finset.mem_univ 1⟩, fun s _ => ?_⟩
  rw [Finset.smul_finset_univ, symmDiff_self]
  simpa using hε

/-- **Trivial groups are amenable.** Every group with at most one element is amenable; the set
$F = \{1\}$ witnesses the Følner condition. -/
theorem isAmenable_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    IsAmenable G := by
  intro K ε hε
  refine ⟨{1}, Finset.singleton_nonempty 1, fun s _ => ?_⟩
  rw [Finset.smul_finset_singleton, Subsingleton.elim (s • (1 : G)) 1, symmDiff_self]
  simpa using hε

/-- **Groups containing a rank-two free subgroup are not amenable.** An injective homomorphism
from the free group on two generators into `G` obstructs the Følner condition on `G`. -/
theorem not_isAmenable_of_freeGroupRankTwo_embedding {G : Type*} [Group G]
    (f : FreeGroup (Fin 2) →* G) (hf : Function.Injective f) : ¬ IsAmenable G := by
  classical
  -- In each right coset of the image, choose a representative and use free-group coordinates.
  let q := Quotient.mk (QuotientGroup.rightRel f.range)
  let rep (g : G) : G := (q g).out
  have hex (g : G) : ∃ x, f x = g * (rep g)⁻¹ :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq (q g)))
  choose coord hcoord using hex
  have hmul (x : FreeGroup (Fin 2)) (g : G) : coord (f x * g) = x * coord g := by
    have hq : q g = q (f x * g) := Quotient.sound <|
      QuotientGroup.rightRel_apply.mpr (by simp [mul_assoc])
    have hr : rep g = rep (f x * g) := congrArg Quotient.out hq
    apply hf
    rw [hcoord, map_mul, hcoord, ← hr, mul_assoc]
  let s (i : Fin 2) := f (FreeGroup.of i)
  intro h
  obtain ⟨F, hF, hFølner⟩ := h {s 0, s 1} (1 / 2) (by norm_num)
  let A (i : Fin 2) (b : Bool) := F.filter fun g => (coord g).toWord.head? = some (i, b)
  let D (i : Fin 2) := (s i • F) ∆ F
  -- Prepending a positive generator either cancels its inverse or gives that first letter.
  have hbound (i : Fin 2) : F.card ≤ (A i false).card + (A i true).card + (D i).card := by
    have hpart : (F \ A i false).card + (A i false).card = F.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    have htranslate : (F \ A i false).card ≤ (A i true ∪ D i).card := by
      refine Finset.card_le_card_of_injOn (s i * ·) (fun g hg => ?_) (mul_right_injective _).injOn
      have hg' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hg)
      change s i * g ∈ A i true ∪ D i
      by_cases hm : s i * g ∈ F
      · apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨hm, ?_⟩
        have hhead : (coord g).toWord.head? ≠ some (i, false) :=
          fun he => hg'.2 (Finset.mem_filter.mpr ⟨hg'.1, he⟩)
        change (coord (f (FreeGroup.of i) * g)).toWord.head? = _
        rw [hmul]
        change (FreeGroup.mk [(i, true)] * coord g).toWord.head? = _
        rw [FreeGroup.toWord_mk_mul_eq]
        simp [hhead]
      · exact Finset.mem_union_right _ <| Finset.mem_symmDiff.mpr <| Or.inl
          ⟨(Finset.mul_mem_smul_finset_iff _).mpr hg'.1, hm⟩
    have hle := htranslate.trans (Finset.card_union_le _ _)
    omega
  -- The four signed first-letter classes are pairwise disjoint subsets of `F`.
  let C (i : Fin 2) := A i false ∪ A i true
  have hd (i : Fin 2) : Disjoint (A i false) (A i true) := by
    rw [Finset.disjoint_left]
    intro g hneg hpos
    have hhead := (Finset.mem_filter.mp hneg).2
    simpa [hhead] using (Finset.mem_filter.mp hpos).2
  have hc : Disjoint (C 0) (C 1) := by
    rw [Finset.disjoint_left]
    simp only [C, A, Finset.mem_union, Finset.mem_filter]
    rintro g (⟨_, h₀⟩ | ⟨_, h₀⟩) (⟨_, h₁⟩ | ⟨_, h₁⟩) <;>
      simp [h₀] at h₁
  have hclasses : (C 0 ∪ C 1).card ≤ F.card := Finset.card_le_card <|
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [Finset.card_union_of_disjoint hc, Finset.card_union_of_disjoint (hd 0),
    Finset.card_union_of_disjoint (hd 1)] at hclasses
  have hcard : F.card ≤ (D 0).card + (D 1).card := by
    have h₀ := hbound 0
    have h₁ := hbound 1
    omega
  have hpos : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hr : 1 ≤ ((D 0).card : ℝ) / F.card + ((D 1).card : ℝ) / F.card := by
    rw [← add_div, ← div_self (ne_of_gt hpos)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos.le
  have h₀ := hFølner (s 0) (by simp)
  have h₁ := hFølner (s 1) (by simp)
  exact (not_lt_of_ge hr) (by simpa only [add_halves] using add_lt_add h₀ h₁)

/-- The symmetric group `S₃` is amenable (an ordinary finite example). -/
example : IsAmenable (Equiv.Perm (Fin 3)) := isAmenable_of_finite _

/-- The trivial group is amenable (a boundary example). -/
example : IsAmenable PUnit := isAmenable_of_subsingleton _
