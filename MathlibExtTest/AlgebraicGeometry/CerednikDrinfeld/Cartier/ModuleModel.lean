/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.ModuleModel

@[expose] public noncomputable section

namespace CartierModuleModelTest

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders: the pieces of the model are the graded pieces. -/
theorem exactSource {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (i : Fin 2)
    (f : CartierModule p X.F) :
    f ∈ (X.toGradedCartierModuleData j hc).piece i ↔ f ∈ X.gradedPiece j (i : ℕ) :=
  mem_toGradedCartierModuleData_piece_iff X j hc i f

/-- Consumer with the original binders: the model's homothety is the Cartier homothety. -/
theorem exactSourceHomothety {B : Type} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (b : B)
    (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).homothety b f = homothety b f :=
  toGradedCartierModuleData_homothety_apply X j hc b f

/-- The model is available over a base ring in a higher universe. -/
example {B : Type 1} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    (X.toGradedCartierModuleData j hc).M = CartierModule p X.F :=
  toGradedCartierModuleData_M X j hc

/-- `ϖ` is linear over the Witt vectors. -/
example {B : Type} [CommRing B] (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.varpiLinear f = endAct X.varpiEnd f :=
  X.varpiLinear_apply f

end CartierModuleModelTest
