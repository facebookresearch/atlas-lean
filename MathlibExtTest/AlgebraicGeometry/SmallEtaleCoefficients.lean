/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues
public import MathlibExt.AlgebraicGeometry.SmallEtaleSignedTateCoefficients
public import MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing

/-!
# Tests for small-étale Tate coefficients, unramified classes and cycle sums
-/

@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.SmallEtaleCoefficients

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.IntegerSchemeChow
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
open MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.SmallEtaleSignedTateCoefficients
open MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
open MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing
open MathlibExt.AlgebraicGeometry.LogPairs

/-- The actual lifted-integer coefficient reduction retains the nonzero Z/2 unit. -/
example : (scalarReduction 2).hom (1 : Scalar) = (1 : FiniteCoefficient 2) := rfl

example : (scalarReduction 2).hom (1 : Scalar) ≠ 0 := by decide

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

section Twists

variable {l : ℕ} (S : Data l) (X : Scheme.{0})

/-- Nonnegative twists are the Tate tensor coefficients themselves. -/
example (j : ℕ) : signedTwist S X j = S.coefficient X j := rfl

/-- Twist `-1` is the internal Hom from `μ_l` to the constant `ℤ/l` coefficient, not a
positive coefficient: no root of unity is chosen. -/
example : signedTwist S X (-1) = coefficientHom X (S.coefficient X 1) (S.coefficient X 0) :=
  rfl

/-- Twist `-(j + 1)` dualizes the `(j + 1)`-st tensor power. -/
example (j : ℕ) :
    signedTwist S X (Int.negSucc j) =
      coefficientHom X (S.coefficient X (j + 1)) (S.coefficient X 0) :=
  rfl

/-- On nonnegative twists, the signed coefficient maps are the Tate pushforward maps. -/
example (D : SignedMaps S) {Y : Scheme.{0}} (f : Y ⟶ X)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤))) (j : ℕ) :
    D.coefficientMap f hX hY j = (S.tate f).map j :=
  rfl

end Twists

section Unramified

variable {l : ℕ} (S : System l)

/-- Unramified classes form a subgroup containing every sum of unramified classes. -/
example (k K : Type) [Field k] [Field K] [Algebra k K] (i : ℤ) (j : ℕ)
    (a b : S.toData.H (Spec (.of K)) i j) (ha : IsUnramified S k K i j a)
    (hb : IsUnramified S k K i j b) : IsUnramified S k K i j (a + b) :=
  (unramifiedSubgroup S k K i j).add_mem ha hb

/-- The local evaluation at a point does not depend on the chosen lifts. -/
example {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (i : ℤ) (j : ℕ)
    (a : varietyUnramified S V i j) (D E : LocalEvaluationData S V i j a) (x : V.X.left) :
    D.evaluate x = E.evaluate x :=
  evaluation_independent D E x

end Unramified

section Cycles

variable {l : ℕ} (S : Data l) {k : Type} [Field k]

/-- The cycle sum of a single closed point is the value at that point, weighted by its
integer coefficient. -/
example (X : FieldScheme k) (P : CycleSupport X) (i : ℤ) (j : ℕ)
    (v : ZeroPoint X → S.H (Spec (.of k)) i j) (c : CycleGroup X.scheme.left 0) :
    cycleSum S X P i j v c =
      (closedCoefficients X P c).sum fun p n ↦ n • v p := by
  rfl

end Cycles

section Multiplicity

open MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace
open _root_.CategoryTheory.Limits

/-- Along the identity of `X`, a geometric point lifts to itself with multiplicity one: the
geometric fibre is the reduced point, whose local ring is a field of length one. -/
example {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : Spec (.of Ω) ⟶ X) :
    fibreMultiplicity (𝟙 X) p ⟨p, Category.comp_id p⟩ = 1 := by
  set b : Spec (.of Ω) ⟶ pullback (𝟙 X) p := pullback.lift p (𝟙 _) (by simp)
  have hfield : IsField ((pullback (𝟙 X) p).presheaf.stalk (b default)) := by
    let y := (pullback.snd (𝟙 X) p) (b default)
    have hy : closure {y} ∈ irreducibleComponents (Spec (.of Ω)) := by
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
      exact Set.eq_univ_of_forall fun z => by
        rw [Subsingleton.elim z y]
        exact subset_closure rfl
    exact (asIso ((pullback.snd (𝟙 X) p).stalkMap (b default))).symm.commRingCatIsoToRingEquiv.isField
      (isField_stalk_of_closure_mem_irreducibleComponents _ y hy)
  letI := hfield.toField
  show (Module.length _ _).toNat = 1
  rw [Module.length_eq_one]
  rfl

end Multiplicity

end MathlibExtTest.AlgebraicGeometry.SmallEtaleCoefficients
