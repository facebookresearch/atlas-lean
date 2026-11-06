/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalData

/-! The complete original Conway word carries both root-eight flag vectors to the canonical flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The three genuine monomial factors and three original Xi factors, in action order. -/
def generatedFifthRootEightCanonicalTransport : leechIsomSubgroup :=
  generatedFifthRootEightCanonicalMonomial 2 * co1XiIsometry * co1XiIsometry *
    generatedFifthRootEightCanonicalMonomial 1 * co1XiIsometry *
    generatedFifthRootEightCanonicalMonomial 0

/-- The integer stage formula is precisely the genuine complete monomial action. -/
theorem generatedFifthRootEight_canonical_monomial_coordinates (k : Fin 3)
    (u : leechIntegral) :
    (leechIntegralAction (generatedFifthRootEightCanonicalMonomial k) u).val =
      generatedFifthRootEightCanonicalMonomialInteger k u.val := by
  rw [generatedFifthRootEightCanonicalMonomial, map_mul, LinearEquiv.mul_apply,
    leechIntegralAction_golaySign, leechIntegralAction_golayPermutation]
  rfl

private theorem monomial_step (k : Fin 3) (u : leechIntegral) (v w : Fin 24 → ℤ)
    (hu : u.val = v) (hw : generatedFifthRootEightCanonicalMonomialInteger k v = w) :
    (leechIntegralAction (generatedFifthRootEightCanonicalMonomial k) u).val = w := by
  rw [generatedFifthRootEight_canonical_monomial_coordinates, hu, hw]

private theorem xi_step (u : leechIntegral) (v w : Fin 24 → ℤ) (hu : u.val = v)
    (hw : co1XiNumerator *ᵥ v = (2 : ℕ) • w) :
    (leechIntegralAction co1XiIsometry u).val = w := by
  funext i
  have he := congrFun (co1Xi_integral_double u) i
  rw [hu, hw] at he
  simp only [Pi.smul_apply, nsmul_eq_mul] at he
  omega

/-- All six actual action stages preserve every coordinate of both original flag vectors. -/
theorem generatedFifthRootEight_canonical_flag_coordinates (b : Bool) :
    (leechIntegralAction generatedFifthRootEightCanonicalTransport
      (if b then generatedFifthRootEightNormFour else generatedFifthRootEightNormSix)).val =
        generatedFifthRootEightCanonicalStages b 6 := by
  let u := if b then generatedFifthRootEightNormFour else generatedFifthRootEightNormSix
  have h0 : u.val = generatedFifthRootEightCanonicalStages b 0 := by
    cases b <;> decide +kernel
  obtain ⟨hm0, hm1, hm2⟩ := generatedFifthRootEight_canonical_monomial_certificates b
  obtain ⟨hx0, hx1, hx2⟩ := generatedFifthRootEight_canonical_xi_certificates b
  let u1 := leechIntegralAction (generatedFifthRootEightCanonicalMonomial 0) u
  have h1 : u1.val = generatedFifthRootEightCanonicalStages b 1 :=
    monomial_step 0 u _ _ h0 hm0
  let u2 := leechIntegralAction co1XiIsometry u1
  have h2 : u2.val = generatedFifthRootEightCanonicalStages b 2 := xi_step u1 _ _ h1 hx0
  let u3 := leechIntegralAction (generatedFifthRootEightCanonicalMonomial 1) u2
  have h3 : u3.val = generatedFifthRootEightCanonicalStages b 3 :=
    monomial_step 1 u2 _ _ h2 hm1
  let u4 := leechIntegralAction co1XiIsometry u3
  have h4 : u4.val = generatedFifthRootEightCanonicalStages b 4 := xi_step u3 _ _ h3 hx1
  let u5 := leechIntegralAction co1XiIsometry u4
  have h5 : u5.val = generatedFifthRootEightCanonicalStages b 5 := xi_step u4 _ _ h4 hx2
  have h6 := monomial_step 2 u5 _ _ h5 hm2
  simpa only [generatedFifthRootEightCanonicalTransport, map_mul, LinearEquiv.mul_apply]
    using h6

/-- The literal genuine transport fixes the normalization of the original norm-four vector. -/
theorem generatedFifthRootEight_canonical_root :
    leechIntegralAction generatedFifthRootEightCanonicalTransport generatedFifthRootEightNormFour =
      leechNormSixHS100Root := by
  apply Subtype.ext
  have h := generatedFifthRootEight_canonical_flag_coordinates true
  have he : generatedFifthRootEightCanonicalStages true 6 = leechNormSixHS100Root.val := by
    decide +kernel
  exact h.trans he

/-- The same complete word sends the original joining vector to the full canonical companion. -/
theorem generatedFifthRootEight_canonical_companion :
    leechIntegralAction generatedFifthRootEightCanonicalTransport generatedFifthRootEightNormSix =
      leechNormSixHS100Companion := by
  apply Subtype.ext
  have h := generatedFifthRootEight_canonical_flag_coordinates false
  have he : generatedFifthRootEightCanonicalStages false 6 = leechNormSixHS100Companion.val := by
    decide +kernel
  exact h.trans he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
