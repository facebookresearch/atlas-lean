/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeAmbientReconstructionMaps

/-!
# Ringed reconstruction from the original evaluation and projection mates

The coefficient left representative maps to the actual source solution
by the counit of `L^E ⊣ Q`; no invertibility of the quotient units is
assumed. The first mate is
the actual ambient coefficient-tensor/module-Hom adjunction, retaining
the endpoint D action. The second mate is actual beta-pull/ringed-alpha
projection. The result is an ordinary D-module map. Its IsIso is an
output requested under holonomicity, never an input.

Source: DK1311.2374v2 Proposition9.5.1 and Theorem9.5.3;
Mathlib56a005 native adjunctions and units, Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeRingedReconstructionMaps

open _root_.CategoryTheory
open NativeAmbientReconstructionMaps

universe uA uN uM uE vA vN vM vE
variable {A : Type uA} {N : Type uN} {M : Type uM} {E : Type uE}
  [Category.{vA} A] [Category.{vN} N] [Category.{vM} M] [Category.{vE} E]
  (Q : N ⥤ E) (Lrep : E ⥤ N) (LQ : Lrep ⊣ Q)
  (tensor : N ⥤ M ⥤ M) [∀ K : N, (tensor.obj K).IsLeftAdjoint]
  (pull : A ⥤ M) (push : M ⥤ A) (projection : pull ⊣ push)

/-- The original evaluation is mated first in the module category and then in ordinary D modules. -/
def reconstructionMap (a : A) (H : N) (O : M)
    (evaluation : (tensor.obj H).obj (pull.obj a) ⟶ O) :
    a ⟶ push.obj (((tensor.obj (Lrep.obj (Q.obj H))).rightAdjoint).obj O) :=
  projection.homEquiv a _
    ((Adjunction.ofIsLeftAdjoint (tensor.obj (Lrep.obj (Q.obj H)))).homEquiv _ _
      ((tensor.map (leftRepresentativeToSource Q Lrep LQ H)).app (pull.obj a) ≫
        evaluation))

end MathlibExt.CategoryTheory.NativeRingedReconstructionMaps
