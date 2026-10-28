/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine equivalence of independent Y444 and original Y555 after checked terminal elimination.
All thirteen-generator relations are the original Coxeter relations and spider10.
Both source maps and their compositions are proved explicitly. This equivalence is a
source presentation reduction; identification with the wreath product of actual G remains open. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444Naturality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTerminalIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Checked original terminal elimination makes the second source-map composition the identity. -/
theorem y444IntoY555_comp_reduction_eq_id :
    y444IntoY555.comp y555IntoY444 = MonoidHom.id BimonsterPresentation := by
  rw [y444IntoY555_comp_reduction, y555TerminalHom_eq_id]

/-- The independent thirteen-generator Coxeter/spider source is the original Y555 quotient. -/
def y444PresentationEquivY555 : Y444Presentation ≃* BimonsterPresentation where
  toFun := y444IntoY555
  invFun := y555IntoY444
  left_inv g := congrArg (fun f : Y444Presentation →* Y444Presentation => f g)
    y555IntoY444_comp_inclusion
  right_inv g := congrArg (fun f : BimonsterPresentation →* BimonsterPresentation => f g)
    y444IntoY555_comp_reduction_eq_id
  map_mul' := y444IntoY555.map_mul

/-- The source equivalence retains the distinguished original central swap generator exactly. -/
theorem y444PresentationEquivY555_center :
    y444PresentationEquivY555 (PresentedGroup.of none) = bimonsterSwap :=
  y444IntoY555_generator none

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
