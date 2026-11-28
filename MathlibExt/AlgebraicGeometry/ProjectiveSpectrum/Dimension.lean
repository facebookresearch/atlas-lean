/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Topology.KrullDimension

/-!
# The dimension of `Proj`

Let `𝒜` be an `ℕ`-grading of a commutative ring `A`.

* `AlgebraicGeometry.Proj.topologicalKrullDim_eq`: the topological Krull dimension of `Proj 𝒜`
  is the Krull dimension of the poset of relevant homogeneous primes of `A`.
* `ProjectiveSpectrum.length_add_one_le_ringKrullDim`: a chain of relevant homogeneous primes of
  length `n` extends to a chain of primes of `A` of length `n + 1` (by a maximal ideal containing
  the last prime and the irrelevant ideal).
* `AlgebraicGeometry.Proj.topologicalKrullDim_lt`: if `dim A ≤ n` then `dim Proj 𝒜 < n`.
* `ringKrullDim_le_of_isIntegral`: an integral algebra has Krull dimension at most that of the base
  (by incomparability).
-/

@[expose] public section

open AlgebraicGeometry

/-- **Integral extensions do not raise the dimension.** If `B` is an integral `A`-algebra, then
`dim B ≤ dim A`: contraction of primes is strictly monotone (incomparability). Injectivity of
`A → B` is not needed for this inequality. -/
theorem ringKrullDim_le_of_isIntegral (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono (fun p : PrimeSpectrum B =>
    (⟨p.asIdeal.under A, inferInstance⟩ : PrimeSpectrum A)) fun _ _ h =>
      Ideal.IsIntegral.under_lt_under h

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The underlying prime ideal of a point of `Proj 𝒜`, as a point of `Spec A`. -/
def toPrimeSpectrum (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum A :=
  ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

theorem strictMono_toPrimeSpectrum : StrictMono (toPrimeSpectrum 𝒜) := fun _ _ h => h

/-- A relevant homogeneous prime is strictly contained in some prime of `A`: a maximal ideal
containing it and the irrelevant ideal. -/
theorem exists_lt_toPrimeSpectrum (x : ProjectiveSpectrum 𝒜) :
    ∃ q : PrimeSpectrum A, toPrimeSpectrum 𝒜 x < q := by
  classical
  have hne : x.asHomogeneousIdeal.toIdeal ⊔ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := (1 : A)))
    have h0 : GradedRing.proj 𝒜 0 a + GradedRing.proj 𝒜 0 b = 1 := by
      rw [← map_add, hab, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem]
    rw [(HomogeneousIdeal.mem_irrelevant_iff 𝒜 b).mp hb, add_zero, GradedRing.proj_apply] at h0
    exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      (h0 ▸ x.asHomogeneousIdeal.isHomogeneous 0 ha))
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  refine ⟨⟨M, hM.isPrime⟩, lt_of_le_of_ne (le_sup_left.trans hle) fun heq => x.not_irrelevant_le ?_⟩
  change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
  exact le_sup_right.trans (hle.trans (le_of_eq (congrArg PrimeSpectrum.asIdeal heq).symm))

/-- **Chains in `Proj` extend in `Spec`.** A chain of relevant homogeneous primes of length `n`
gives a chain of primes of `A` of length `n + 1`, so its length plus one is at most `dim A`. -/
theorem length_add_one_le_ringKrullDim (l : LTSeries (ProjectiveSpectrum 𝒜)) :
    (l.length + 1 : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨q, hq⟩ := exists_lt_toPrimeSpectrum 𝒜 l.last
  let l' := (l.map _ (strictMono_toPrimeSpectrum 𝒜)).snoc q (by simpa using hq)
  have := Order.LTSeries.length_le_krullDim l'
  simpa [l', ringKrullDim] using this

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

instance : QuasiSober (ProjectiveSpectrum 𝒜) := inferInstanceAs (QuasiSober (Proj 𝒜))

instance : T0Space (ProjectiveSpectrum 𝒜) := inferInstanceAs (T0Space (Proj 𝒜))

/-- **The topological dimension of `Proj`.** The topological Krull dimension of `Proj 𝒜` equals
the Krull dimension of the poset of relevant homogeneous primes of `A` (ordered by inclusion):
irreducible closed subsets correspond to their generic points, reversing inclusion. -/
theorem topologicalKrullDim_eq :
    topologicalKrullDim (Proj 𝒜) = Order.krullDim (ProjectiveSpectrum 𝒜) := by
  change topologicalKrullDim (ProjectiveSpectrum 𝒜) = _
  rw [← Order.krullDim_orderDual]
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono
      (fun Z : TopologicalSpace.IrreducibleCloseds (ProjectiveSpectrum 𝒜) =>
        OrderDual.toDual Z.isIrreducible.genericPoint) fun Z₁ Z₂ h => ?_
    have h₁ := Z₁.isIrreducible.isGenericPoint_genericPoint_closure
    have h₂ := Z₂.isIrreducible.isGenericPoint_genericPoint_closure
    rw [Z₁.isClosed.closure_eq] at h₁
    rw [Z₂.isClosed.closure_eq] at h₂
    refine lt_of_le_of_ne ?_ fun heq => h.ne ?_
    · refine OrderDual.toDual_le_toDual.mpr ((ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mpr ?_)
      have hmem : Z₁.isIrreducible.genericPoint ∈ (Z₂ : Set (ProjectiveSpectrum 𝒜)) := h.le h₁.mem
      rwa [← h₂.def] at hmem
    · ext1
      rw [← h₁.def, ← h₂.def]
      exact congrArg (fun x => closure {OrderDual.ofDual x}) heq
  · refine Order.krullDim_le_of_strictMono
      (fun x : (ProjectiveSpectrum 𝒜)ᵒᵈ =>
        (⟨closure {OrderDual.ofDual x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
          TopologicalSpace.IrreducibleCloseds (ProjectiveSpectrum 𝒜))) fun x y h => ?_
    have hyx : OrderDual.ofDual y < OrderDual.ofDual x := h
    refine lt_of_le_of_ne ?_ fun heq => hyx.ne ?_
    · change closure {OrderDual.ofDual x} ⊆ closure {OrderDual.ofDual y}
      exact closure_minimal (Set.singleton_subset_iff.mpr
        ((ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp hyx.le)) isClosed_closure
    · have := congrArg TopologicalSpace.IrreducibleCloseds.carrier heq
      exact (inseparable_iff_closure_eq.mpr this.symm).eq

/-- **Dimension of `Proj` versus the graded ring.** If `dim A ≤ n`, then the topological Krull
dimension of `Proj 𝒜` is `< n`. -/
theorem topologicalKrullDim_lt {n : ℕ} (h : ringKrullDim A ≤ n) :
    topologicalKrullDim (Proj 𝒜) < n := by
  rw [topologicalKrullDim_eq, Order.krullDim_lt_coe_iff]
  intro l
  have := (ProjectiveSpectrum.length_add_one_le_ringKrullDim 𝒜 l).trans h
  have h' : l.length + 1 ≤ n := by exact_mod_cast this
  exact_mod_cast h'

end AlgebraicGeometry.Proj
