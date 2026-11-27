/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DivisorDynamics

/-!
# Degree growth and nef eigenclasses of actual endomorphisms

These statements concern a finite dominant endomorphism of an actual
smooth projective variety, actual iterated ample pullbacks and actual
curve-degree functions. The limit is not an arbitrary supplied invariant.

References: Truong, *Relative dynamical degrees of correspondences over
a field of arbitrary characteristic*, Journal für die reine und angewandte
Mathematik 758 (2020), 139–182, Theorem 1.1(1);
https://arxiv.org/abs/1605.05049
Numerical Perron–Frobenius supplies the nef eigenclass.

Foliation brackets, saturated tangent distributions, algebraicity of leaves,
height growth and entropy comparisons remain additional interfaces.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DivisorDynamicsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry (ProjectiveSpace.IsProjective)
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.DivisorDynamics
open Filter Topology

universe u

theorem_wanted degreeGrowth_converges (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom] [IsNoetherian X.left]
    (d : ℕ) (hd : 0 < d) [SmoothOfRelativeDimension d X.hom]
    (projective : ProjectiveSpace.IsProjective X) (H : LineBundle X.left)
    (ample : IsAmpleLine H) (f : X ⟶ X) [IsFinite f.left] [IsDominant f.left] :
    0 < firstDynamicalDegree d (topologicalKrullDim_eq_of_smooth X d) hd H ample f ∧
      Tendsto (degreeGrowth d (topologicalKrullDim_eq_of_smooth X d) hd H f) atTop
        (𝓝 (firstDynamicalDegree d (topologicalKrullDim_eq_of_smooth X d) hd H ample f))

theorem_wanted firstDynamicalDegree_independent (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom] [IsNoetherian X.left]
    (d : ℕ) (hd : 0 < d) [SmoothOfRelativeDimension d X.hom]
    (projective : ProjectiveSpace.IsProjective X) (H : LineBundle X.left)
    (ample : IsAmpleLine H) (f : X ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (H' : LineBundle X.left) (ample' : IsAmpleLine H') :
    firstDynamicalDegree d (topologicalKrullDim_eq_of_smooth X d) hd H ample f =
      firstDynamicalDegree d (topologicalKrullDim_eq_of_smooth X d) hd H' ample' f

def_wanted nefEigenclass (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom] [IsNoetherian X.left]
    (d : ℕ) (hd : 0 < d) [SmoothOfRelativeDimension d X.hom]
    (projective : ProjectiveSpace.IsProjective X) (H : LineBundle X.left)
    (ample : IsAmpleLine H) (f : X ⟶ X) [IsFinite f.left] [IsDominant f.left] :
    {v : NDiv X // v ≠ 0 ∧ IsNefClass v ∧
      ∀ C, v.val (composeCurve f C) =
        firstDynamicalDegree d (topologicalKrullDim_eq_of_smooth X d) hd H ample f *
          v.val C}

end WantedExt.AlgebraicGeometry.DivisorDynamicsWanted
