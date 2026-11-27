/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsFiniteTensorTransition

/-!
# Finite tensor transition tests

An elementwise corollary removes the universe lift from the pure-tensor transition equality.

Source: Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral p-adic Hodge theory*,
BMS19 arXiv:1802.03261v2, Theorem1.12(3), footnote3, Sections5.1/7.3/7.4;
Bhatt–Scholze, *Prisms and Prismatic Cohomology*, arXiv:1905.08229v4, Sections12–15.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.CompletedFilteredPrismaticTensorsFiniteTensorTransition

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry AbsolutePrismaticBasis PrismaticFilteredTwists
open CompletedFilteredPrismaticTensors
open scoped TensorProduct

private theorem pure_tensor_down
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (n : ℕ) (B : ((Basis p A)ᵒᵖ)ᵒᵖ)
    (f : (T.data.dual (n + 1)).obj B) (x : (T.data.line (n + 1)).obj B) :
    (((tensorPresheafStep p A D Z T n).app B).hom
      (ULift.up (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x))).down =
    finiteDualStepValue T.data n B f ⊗ₜ[(quotientPresheaf p A D n).obj B]
      finiteLineStepValue T.data n B x := by
  exact congrArg ULift.down
    ((WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors.finiteTensorTransition
      p A D Z T).pure_tensor n B f x)

end MathlibExtTest.AlgebraicGeometry.CompletedFilteredPrismaticTensorsFiniteTensorTransition
