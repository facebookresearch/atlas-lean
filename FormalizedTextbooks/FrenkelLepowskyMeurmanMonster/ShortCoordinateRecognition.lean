/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.RankOneSquareSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortSpanIsometry

/-! Recognition of a signed short-coordinate action from its matrix squares.
The hypotheses concern real linear maps only; no centralizer or lattice action
is assumed. The matrix-square identity is needed only on coordinate vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A unit vector in the actual short-coordinate space. -/
noncomputable def shortCoordinateUnit (r : GriessShortIndex) : GriessShortIndex → ℝ :=
  Pi.single r 1

/-- The matrix component of the square of a pure short-coordinate vector. -/
noncomputable def shortCoordinateSquare (X : GriessShortIndex → ℝ) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  ∑ r, X r ^ 2 • Matrix.vecMulVec (griessShortVector r) (griessShortVector r)

/-- A normalized rank-one image recognizes both the short coordinate and the
corresponding physical short line. -/
theorem shortCoordinateRecognition_singleton
    (F : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ))
    (R : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hF : ∀ X Y, (∑ r, F X r * F Y r) = ∑ r, X r * Y r)
    (hR : ∀ u v, stdPairingFun (R u) (R v) = stdPairingFun u v)
    (hsquare : ∀ r, shortCoordinateSquare (F (shortCoordinateUnit r)) =
      Matrix.vecMulVec (R (griessShortVector r)) (R (griessShortVector r)))
    (r : GriessShortIndex) :
    ∃ s : GriessShortIndex,
      (F (shortCoordinateUnit r) = shortCoordinateUnit s ∨
        F (shortCoordinateUnit r) = -shortCoordinateUnit s) ∧
      (R (griessShortVector r) = griessShortVector s ∨
        R (griessShortVector r) = -griessShortVector s) := by
  classical
  have hv : R (griessShortVector r) ≠ 0 := by
    intro h
    exact centralizer_shortVector_ne_zero r (R.injective (by simpa using h))
  have hn : (∑ s, F (shortCoordinateUnit r) s ^ 2) = 1 := by
    simpa [pow_two, shortCoordinateUnit, Pi.single_apply] using
      hF (shortCoordinateUnit r) (shortCoordinateUnit r)
  obtain ⟨s, hs, hzero⟩ := rankOneSquareSupport_normalized_singleton
    griessShortVector (F (shortCoordinateUnit r)) (R (griessShortVector r)) hv
    centralizer_shortVector_ne_zero
    (fun a b t _ h => centralizer_shortVector_line_unique a b t h) (hsquare r) hn
  have hs0 : F (shortCoordinateUnit r) s ≠ 0 := by rcases hs with h | h <;> simp [h]
  obtain ⟨a, ha⟩ := rankOneSquareSupport_scalar
    griessShortVector (F (shortCoordinateUnit r)) (R (griessShortVector r)) hv
    (hsquare r) s hs0
  have ha0 : a ≠ 0 := by
    intro h
    exact centralizer_shortVector_ne_zero s (by simpa [h] using ha)
  have hline : R (griessShortVector r) = a⁻¹ • griessShortVector s := by
    rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  refine ⟨s, ?_, ?_⟩
  · rcases hs with hs | hs
    · left
      funext t
      by_cases ht : t = s
      · subst t; simpa [shortCoordinateUnit] using hs
      · simpa [shortCoordinateUnit, Pi.single_apply, ht] using hzero t ht
    · right
      funext t
      by_cases ht : t = s
      · subst t; simpa [shortCoordinateUnit] using hs
      · simpa [shortCoordinateUnit, Pi.single_apply, ht] using hzero t ht
  · rcases leechShort_orthogonal_scalar_sign R hR r s a⁻¹ hline with h | h
    · exact Or.inl (by simpa [h] using hline)
    · exact Or.inr (by simpa [h] using hline)

/-- Distinct coordinate unit vectors do not lie on a common signed line. -/
theorem shortCoordinateUnit_sign_unique (r s : GriessShortIndex)
    (h : shortCoordinateUnit r = shortCoordinateUnit s ∨
      shortCoordinateUnit r = -shortCoordinateUnit s) : r = s := by
  classical
  by_contra hrs
  rcases h with h | h <;>
    have he := congrFun h r <;>
    simp [shortCoordinateUnit, hrs] at he

/-- The matrix-square and orthogonality hypotheses force a genuine finite
permutation of coordinates, with independent signs on coordinates and vectors. -/
theorem shortCoordinateRecognition_signed_permutation
    (F : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ))
    (R : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hF : ∀ X Y, (∑ r, F X r * F Y r) = ∑ r, X r * Y r)
    (hR : ∀ u v, stdPairingFun (R u) (R v) = stdPairingFun u v)
    (hsquare : ∀ r, shortCoordinateSquare (F (shortCoordinateUnit r)) =
      Matrix.vecMulVec (R (griessShortVector r)) (R (griessShortVector r))) :
    ∃ p : Equiv.Perm GriessShortIndex, ∀ r,
      (F (shortCoordinateUnit r) = shortCoordinateUnit (p r) ∨
        F (shortCoordinateUnit r) = -shortCoordinateUnit (p r)) ∧
      (R (griessShortVector r) = griessShortVector (p r) ∨
        R (griessShortVector r) = -griessShortVector (p r)) := by
  classical
  choose σ hσ using shortCoordinateRecognition_singleton F R hF hR hsquare
  have hi : Function.Injective σ := by
    intro r t hrt
    have ht : F (shortCoordinateUnit t) = shortCoordinateUnit (σ r) ∨
        F (shortCoordinateUnit t) = -shortCoordinateUnit (σ r) := by
      simpa only [hrt] using (hσ t).1
    have hpair : F (shortCoordinateUnit r) = F (shortCoordinateUnit t) ∨
        F (shortCoordinateUnit r) = -F (shortCoordinateUnit t) := by
      rcases (hσ r).1 with hr | hr <;> rcases ht with ht | ht <;> simp [hr, ht]
    apply shortCoordinateUnit_sign_unique
    rcases hpair with h | h
    · exact Or.inl (F.injective h)
    · exact Or.inr (F.injective (by simpa only [map_neg] using h))
  exact ⟨Equiv.ofBijective σ ⟨hi, Finite.surjective_of_injective hi⟩, hσ⟩

/-- Lattice preservation is a conclusion of the matrix-square identities. -/
theorem shortCoordinateRecognition_mem_isometry
    (F : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ))
    (R : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hF : ∀ X Y, (∑ r, F X r * F Y r) = ∑ r, X r * Y r)
    (hR : ∀ u v, stdPairingFun (R u) (R v) = stdPairingFun u v)
    (hsquare : ∀ r, shortCoordinateSquare (F (shortCoordinateUnit r)) =
      Matrix.vecMulVec (R (griessShortVector r)) (R (griessShortVector r))) :
    R ∈ leechIsomSubgroup := by
  apply leechShort_signed_mem_isometry R hR
  intro r
  obtain ⟨s, _, hs⟩ := shortCoordinateRecognition_singleton F R hF hR hsquare r
  exact ⟨s, hs⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
