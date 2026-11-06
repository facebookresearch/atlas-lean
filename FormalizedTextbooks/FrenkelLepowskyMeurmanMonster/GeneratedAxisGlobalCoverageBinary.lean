/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover

/-! The complete binary-certificate mechanism for real axis coverage.
Local descent edges establish the binary orbit cover; the genuine singleton
resolves the lost sign; actual τ and τ⁻¹ vector transports then prove closure. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The source singleton exchanges the two actual triality transitions on every vector. -/
theorem generatedAxisGlobal_singleton_triality_exchange (x : GriessSpace) :
    sExtra (rhoLocal (inclQ singletonCocodeQ) x) =
      rhoLocal (inclQ singletonCocodeQ) (sExtra⁻¹ x) := by
  let a := rhoLocal (inclQ singletonCocodeQ)
  have hs : a * a = 1 := by
    change rhoLocal (inclQ singletonCocodeQ) * rhoLocal (inclQ singletonCocodeQ) = 1
    rw [← map_mul, ← map_mul]
    change rhoLocal (inclQ (cocodeQ _ * cocodeQ _)) = 1
    rw [cocodeQ_square, map_one, map_one]
  have hi : a⁻¹ = a := inv_eq_of_mul_eq_one_left hs
  have hc : a * sExtra * a = sExtra⁻¹ := by
    simpa only [a, hi] using singletonCocodeQ_conjugates_sExtra_inverse
  have he : sExtra * a = a * sExtra⁻¹ := by
    calc
      sExtra * a = (a * a) * sExtra * a := by rw [hs, one_mul]
      _ = a * (a * sExtra * a) := by group
      _ = a * sExtra⁻¹ := by rw [hc]
  exact LinearEquiv.congr_fun he x

/-- Verified descending binary edges, genuine local stabilizer membership,
and both actual real triality transports imply coverage of every local element. -/
theorem generatedAxisGlobal_triality_of_binary_descent {ι κ : Type*}
    (v : ι → GriessSpace) (C : ι → Subgroup H) (r : ι → κ → H)
    (label : ι → generatedAxisGlobalBinaryOrbit → κ)
    (rank : ι → generatedAxisGlobalBinaryOrbit → ℕ)
    (hfix : ∀ i c, c ∈ C i → rhoLocal c (v i) = v i)
    (hedge : ∀ i x,
      x = generatedAxisGlobalBinaryRoot (r i (label i x)) ∨ ∃ y c,
        c ∈ C i ∧ rank i y < rank i x ∧ label i y = label i x ∧
          generatedAxisGlobalBinaryAct c y = x)
    (hpositive : ∀ i j,
      sExtra (rhoLocal (r i j) (v i)) ∈ generatedLocalOrbitUnion v)
    (hnegative : ∀ i j,
      sExtra⁻¹ (rhoLocal (r i j) (v i)) ∈ generatedLocalOrbitUnion v) :
    Set.MapsTo sExtra (generatedLocalOrbitUnion v) (generatedLocalOrbitUnion v) := by
  rintro x ⟨i, h, rfl⟩
  obtain ⟨j, n, c, hn, hc, he⟩ := generatedAxisGlobal_decompose_of_binary_descent
    (C i) (r i) (label i) (rank i) (hedge i) h
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hfix i c hc]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (r i j) (v i))
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i j)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hfix i c hc]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * r i j) (v i))
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
