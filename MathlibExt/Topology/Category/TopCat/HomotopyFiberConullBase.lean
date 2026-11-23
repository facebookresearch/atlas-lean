/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

/-!
# The actual homotopy-fiber projection over a weakly contractible base

The only weak-equivalence input is the terminal map of the original base.
The proof uses the existing changing-base homotopy-fiber map. Its target
is a homotopy fiber over PUnit, whose left projection is an isomorphism.
Both the point coordinate and the entire compact-open path coordinate are
unique. No fibration, CW structure, contraction or homotopy-fiber comparison
is supplied as a premise.

-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TopCat

private theorem punitPath_hom_ext {A : TopCat.{u}}
    (f g : A ⟶ pathObject (TopCat.of PUnit.{u + 1})) : f = g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro t
  exact Subsingleton.elim _ _

private def homotopyFiberPUnitIso {A : TopCat.{u}}
    (p : A ⟶ TopCat.of PUnit.{u + 1}) (b : TopCat.of PUnit.{u + 1}) :
    homotopyFiber p b ≅ A := by
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let point : A ⟶ P := TopCat.const PUnit.unit
  let pair : A ⟶ A ⨯ P := Limits.prod.lift (𝟙 A) point
  let paths : A ⟶ pathObject P :=
    TopCat.ofHom (ContinuousMap.const A (ContinuousMap.const TopCat.I.{u} b))
  have square : pair ≫ Limits.prod.map p (TopCat.const b) =
      paths ≫ pathEndpoints P := by
    apply Limits.prod.hom_ext
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · exact TopCat.isTerminalPUnit.hom_ext _ _
  let lift : A ⟶ homotopyFiber p b := pullback.lift pair paths square
  have lift_left : lift ≫ homotopyFiberToTotal p b = 𝟙 A := by
    calc
      lift ≫ homotopyFiberToTotal p b =
          (lift ≫ pullback.fst (Limits.prod.map p (TopCat.const b))
            (pathEndpoints P)) ≫ Limits.prod.fst :=
        (Category.assoc _ _ _).symm
      _ = pair ≫ Limits.prod.fst := congrArg
        (fun k : A ⟶ A ⨯ P => k ≫ (Limits.prod.fst : A ⨯ P ⟶ A))
        (pullback.lift_fst pair paths square)
      _ = 𝟙 A := Limits.prod.lift_fst (𝟙 A) point
  have left_lift : homotopyFiberToTotal p b ≫ lift =
      𝟙 (homotopyFiber p b) := by
    apply homotopyPullback_hom_ext
    · rw [Category.assoc, lift_left, Category.comp_id, Category.id_comp]
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · exact punitPath_hom_ext _ _
  exact
    { hom := homotopyFiberToTotal p b
      inv := lift
      hom_inv_id := left_lift
      inv_hom_id := lift_left }

/-- The literal compact-open homotopy-fiber projection is weak when the
terminal map of its original base is weak. No comparison-map weakness is
an input. The result applies at every actual chosen base point. -/
theorem homotopyFiberToTotal_mem_of_base_conull {A B : TopCat.{u}}
    (p : A ⟶ B) (b : B)
    (hB : weakHomotopyEquivalences (terminal.from B)) :
    weakHomotopyEquivalences (homotopyFiberToTotal p b) := by
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let h : B ⟶ P := terminal.from B ≫ TopCat.terminalIsoPUnit.hom
  let q : A ⟶ P := TopCat.const PUnit.unit
  have square : p ≫ h = (𝟙 A) ≫ q :=
    TopCat.isTerminalPUnit.hom_ext _ _
  have hWeak : weakHomotopyEquivalences h :=
    MorphismProperty.RespectsIso.postcomp weakHomotopyEquivalences
      TopCat.terminalIsoPUnit.hom (terminal.from B) hB
  let m : homotopyFiber p b ⟶ homotopyFiber q (h b) :=
    homotopyFiberMapOfSquare (p := p) (q := q) (𝟙 A) h square b
  have mWeak : weakHomotopyEquivalences m :=
    homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences
      (p := p) (q := q) (𝟙 A) h square b
      (weakHomotopyEquivalences.id_mem A) hWeak
  let e : homotopyFiber q (h b) ≅ A := homotopyFiberPUnitIso q (h b)
  have targetWeak : weakHomotopyEquivalences e.hom :=
    weakHomotopyEquivalences.of_isIso e.hom
  have compositeWeak : weakHomotopyEquivalences (m ≫ e.hom) :=
    weakHomotopyEquivalences.comp_mem m e.hom mWeak targetWeak
  have composite_eq : m ≫ e.hom = homotopyFiberToTotal p b :=
    (homotopyFiberMapOfSquare_toTotal (p := p) (q := q)
      (𝟙 A) h square b).trans (Category.comp_id _)
  exact composite_eq ▸ compositeWeak

end TopCat

end
