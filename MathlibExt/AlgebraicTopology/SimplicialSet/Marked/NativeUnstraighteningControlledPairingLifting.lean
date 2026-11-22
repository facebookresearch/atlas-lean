/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningControlledPairingStage

/-!
# The whole original controlled pairing lifts actual native Un maps

Each SAME original rank stage lifts through actual original inner or
marked critical native cells. The ENTIRE original marked transfinite
filtration and its unchanged colimit map therefore lift under the SAME
native Un map of an ACTUAL coherent-model fibration. All original ranks,
source markings and whole map equations are retained. No target or
source fibrancy, Kan base/scalar, or supplied native filler is needed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (ambient : Marked.{u}) (A : ambient.toSSet.Subcomplex) (P : A.Pairing) [P.IsRegular]

/-- The SAME whole original controlled marked pairing inclusion lifts against native Un of every ACTUAL
coherent-model fibration by its ENTIRE original rank filtration. -/
theorem nativeUnstraightening_controlledPairing_lifting
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CartesianControlledPairing ambient A P) (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (comapHom ambient A.ι) ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p := ((nativeUnstraightening B).map q).left
  let W : MorphismProperty Marked.{u} := (ofHoms (fun _ : Unit => p)).llp
  let h := pairingFiltrationTransfiniteComposition ambient A P hmarks
  let hw : W.TransfiniteCompositionOfShape ℕ (comapHom ambient A.ι) :=
    { toTransfiniteCompositionOfShape := h
      map_mem j _ := by
        intro U V f hf
        obtain ⟨i⟩ := hf
        exact nativeUnstraightening_controlledPairing_step_lifting ambient A P hmarks hP B q j hq }
  have hW : W (comapHom ambient A.ι) := (transfiniteCompositionsOfShape_le W ℕ) _ ⟨hw⟩
  exact hW _ (ofHoms.mk ())

end SSet.Marked
