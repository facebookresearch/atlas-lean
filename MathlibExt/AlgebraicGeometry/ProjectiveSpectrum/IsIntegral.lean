/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Properties

/-!
# `Proj` of a graded domain is integral

Let `𝒜` be an `ℕ`-grading of a commutative ring `A`. If `A` is a domain and some homogeneous
element of positive degree is nonzero, then `Proj 𝒜` is an integral scheme.

The zero ideal is then a relevant homogeneous prime, and it lies below every homogeneous prime, so
its point is dense: `Proj 𝒜` is irreducible. Every stalk of `Proj 𝒜` is a homogeneous localization
`A_(𝔭)`, a subring of the localization `A_𝔭` of the domain `A`, hence reduced.

## Main results

* `ProjectiveSpectrum.irreducibleSpace_of_isDomain`: `Proj 𝒜` is irreducible.
* `AlgebraicGeometry.Proj.isReduced_of_isReduced`: `Proj 𝒜` is reduced when `A` is reduced.
* `AlgebraicGeometry.Proj.isIntegral_of_isDomain`: `Proj 𝒜` is integral.

## References

* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015), §2, p. 2.
* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, Chapter II, §1, p. 46.
-/

@[expose] public section

open AlgebraicGeometry

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- If `A` is a domain and `𝒜` has a nonzero homogeneous element of positive degree, the zero ideal
is a relevant homogeneous prime: the point of `Proj 𝒜` it defines. -/
def botPoint [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, a ≠ 0) : ProjectiveSpectrum 𝒜 :=
  ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, by
    obtain ⟨i, hi, a, ha, ha0⟩ := h
    intro hle
    have : a ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 ha hi.ne']
    have h0 := hle this
    rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot] at h0
    exact ha0 ((Submodule.mem_bot _).mp h0)⟩

@[simp]
theorem botPoint_asHomogeneousIdeal [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, a ≠ 0) :
    (botPoint 𝒜 h).asHomogeneousIdeal = ⊥ :=
  rfl

/-- The point of `Proj 𝒜` given by the zero ideal is dense (a generic point). -/
theorem closure_botPoint [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, a ≠ 0) :
    closure {botPoint 𝒜 h} = Set.univ :=
  Set.eq_univ_of_forall fun y => (le_iff_mem_closure 𝒜 _ y).mp
    (show (⊥ : HomogeneousIdeal 𝒜) ≤ y.asHomogeneousIdeal from bot_le)

/-- **`Proj` of a graded domain is irreducible.** If `A` is a domain and the grading `𝒜` has a
nonzero homogeneous element of positive degree, the projective spectrum of `𝒜` is an irreducible
topological space; the zero ideal is its generic point. -/
theorem irreducibleSpace_of_isDomain [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, a ≠ 0) :
    IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
  have hirr := (isIrreducible_singleton (x := botPoint 𝒜 h)).closure
  rw [closure_botPoint 𝒜 h] at hirr
  exact (irreducibleSpace_def _).mpr hirr

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- **`Proj` of a reduced graded ring is reduced.** If `A` is reduced, then `Proj 𝒜` is a reduced
scheme: each stalk is a homogeneous localization `A_(𝔭)`, a subring of the localization `A_𝔭`. -/
theorem isReduced_of_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have : ∀ x : Proj 𝒜, _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := fun x => by
    have := x.isPrime
    let v : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →*₀
        Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
      { toFun := HomogeneousLocalization.val
        map_zero' := HomogeneousLocalization.val_zero
        map_one' := HomogeneousLocalization.val_one
        map_mul' := HomogeneousLocalization.val_mul }
    have := isReduced_of_injective v (HomogeneousLocalization.val_injective _)
    exact isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

/-- **`Proj` of a graded domain is integral.** Let `𝒜` be an `ℕ`-grading of a commutative ring
`A`. If `A` is a domain and some homogeneous element of positive degree is nonzero, then `Proj 𝒜` is
an integral scheme. (Used for the Weierstrass cubic of B. Conrad, "Minimal models for elliptic
curves", §2, p. 2, and J. S. Milne, *Elliptic Curves*, 2nd ed., Ch. II, §1, p. 46.) -/
theorem isIntegral_of_isDomain [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, a ≠ 0) :
    IsIntegral (Proj 𝒜) := by
  have := isReduced_of_isReduced 𝒜
  have : IrreducibleSpace (Proj 𝒜) := ProjectiveSpectrum.irreducibleSpace_of_isDomain 𝒜 h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Proj
