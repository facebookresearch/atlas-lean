/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GradedConeProjectiveModels

/-!
# General cone Segre components and supported Chern degrees

Segre classes are defined from the actual completion P(C⊕1): apply
powers of its normalized c_1(O(1)) to every dimension component of
the genuine generic-length fundamental cycle, then push along its
proper projection. This also handles nonpure cones. No vector-bundle
projective Segre formula is substituted for a general cone.

The Chern–Segre number is the actual zero-dimensional degree of
c(E)∩s(C), with all Chern operations rooted in the native integral
zero-section/projective construction. It supplies the operation in
Behrend's Euler-obstruction equation (3).

References: Fulton, Intersection Theory, §4.1; Behrend,
arXiv:math/0507523v2, §1.2, equation (3).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConeSegreOperations

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open IntegralChowChernModels GradedConeProjectiveModels StackCycleGeometry

variable {X : SchemeData}

/-- Every component uses the actual generic local-ring lengths of the completion. -/
def fundamentalChow (Y : SchemeData) (d : ℤ) : Chow Y d :=
  IntegerSchemeChow.cycleClass Y d
    (IntegerSchemeChow.dimensionPart Y.scheme.left d (integralFundamentalCycle Y.scheme.left))

/-- The proof adapters concern fixed proper/zero-section maps of this completion. -/
structure SegreData (C : GlobalGradedCone X) where
  completion : GlobalCompletion C
  lineTotal : LineTotalModel completion.total completion.hyperplane
  lineChow : LineChowComparison lineTotal
  push : ProperPushDescent completion.projection
  dimensionBound : ℕ
  bound : topologicalKrullDim completion.total.scheme.left ≤ (dimensionBound : ℕ)

/-- The general cone's dimension-d Segre component p_*(Σ_k ξ^(k−d)[P(C⊕1)]_k). -/
def segreComponent {C : GlobalGradedCone X} (D : SegreData C) (d : ℤ) : Chow X d :=
  ∑ k ∈ Finset.range (D.dimensionBound+1),
    if h : d≤(k : ℤ) then
      (properPush D.push d)
        (chowCast D.completion.total (by
          have he : (((k : ℤ)-d).toNat : ℤ) = (k : ℤ)-d :=
            Int.toNat_of_nonneg (by omega)
          omega)
          (firstChernPower D.lineTotal D.lineChow ((k : ℤ)-d).toNat (k : ℤ)
            (fundamentalChow D.completion.total (k : ℤ))))
    else 0

/-- The dimension-zero part of c(E)∩s(C), from the actual all-rank Chern caps. -/
def chernSegreZero {C : GlobalGradedCone X} (D : SegreData C)
    {E : X.scheme.left.Modules} {r : ℕ} (K : ChernConstruction X E r) : Chow X 0 :=
  ∑ i ∈ Finset.range (r+1),
    chowCast X (by omega) (chernCap K i (i : ℤ) (segreComponent D (i : ℤ)))

/-- The source-supported Chern–Segre degree uses the actual residue-degree comparison. -/
def chernSegreDegree [IsProper X.scheme.hom] {C : GlobalGradedCone X}
    (D : SegreData C) {E : X.scheme.left.Modules} {r : ℕ} (K : ChernConstruction X E r)
    (degree : IntegerSchemeChow.DegreeComparison X) : ℤ :=
  degree.degree (chernSegreZero D K)

end MathlibExt.AlgebraicGeometry.ConeSegreOperations
