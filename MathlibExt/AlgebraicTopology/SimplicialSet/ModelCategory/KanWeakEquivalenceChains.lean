/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyEquiv
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedQuasiIso
import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor

/-!
# Chain invariance under weak equivalences of Kan complexes

A weak equivalence between Kan complexes has a literal simplicial homotopy
inverse by the simplicial Whitehead theorem.  Applying the existing chain
homotopy-equivalence theorem gives the unnormalized result.  The normalized
result follows from naturality of the normalized-chain inclusion and
quasi-isomorphism cancellation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Limits

universe w v u

namespace SSet.KanComplex.W

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

/-- A weak equivalence between Kan complexes induces a quasi-isomorphism on
unnormalized simplicial chains. -/
theorem quasiIso_chainComplexMap
    {X Y : SSet.{w}} {f : X ⟶ Y} (hf : SSet.KanComplex.W f) (A : C) :
    QuasiIso (SSet.chainComplexMap f A) := by
  let _ : SSet.KanComplex X := hf.kanComplex_source
  let _ : SSet.KanComplex Y := hf.kanComplex_target
  obtain ⟨g, Hfg, Hgf⟩ := hf.exists_homotopy_inverse
  exact SSet.quasiIso_chainComplexMap_of_simplicialHomotopyEquiv
    f g Hfg.some.toSimplicialObjectHomotopy
      Hgf.some.toSimplicialObjectHomotopy A

/-- A weak equivalence between Kan complexes induces a quasi-isomorphism on
normalized simplicial chains. -/
theorem quasiIso_normalizedChainComplexMap
    {X Y : SSet.{w}} {f : X ⟶ Y} (hf : SSet.KanComplex.W f) (A : C) :
    QuasiIso (SSet.normalizedChainComplexMap f A) := by
  let nf := SSet.normalizedChainComplexMap f A
  let ix := X.fromNormalizedChainComplex A
  let iy := Y.fromNormalizedChainComplex A
  let cf := SSet.chainComplexMap f A
  let _ : QuasiIso cf := quasiIso_chainComplexMap hf A
  let _ : QuasiIso ix := inferInstance
  let _ : QuasiIso iy := inferInstance
  have hnat : nf ≫ iy = ix ≫ cf :=
    (SSet.fromNormalizedChainComplexNatTrans (C := C) A).naturality f
  have hcomp : QuasiIso (nf ≫ iy) := by
    rw [hnat]
    infer_instance
  let _ : QuasiIso (nf ≫ iy) := hcomp
  exact quasiIso_of_comp_right nf iy

end SSet.KanComplex.W
