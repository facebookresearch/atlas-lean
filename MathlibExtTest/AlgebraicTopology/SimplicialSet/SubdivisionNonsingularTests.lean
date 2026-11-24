/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Nonsingular

/-!
# Nonsingular subdivision consumers

Persistent public-only clients for the subdivision comparison and the
nonsingularity of one-step and iterated subdivision.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionNonsingularTests

universe u

section PublicAPI

example : SSet.{u} ⥤ SSet.{u} :=
  SSet.nondegenerateNerve

example : SSet.sd.{u} ⟶ SSet.nondegenerateNerve.{u} :=
  SSet.sdToNondegenerateNerve

example (X : SSet.{u}) [X.Nonsingular] :
    SSet.sd.obj X ≅ SSet.nondegenerateNerve.obj X :=
  SSet.sdIsoNondegenerateNerve X

example (X : SSet.{u}) [X.Nonsingular] :
    (SSet.sdIsoNondegenerateNerve X).hom =
      SSet.sdToNondegenerateNerve.app X := by
  simp

/-- error: failed to synthesize instance of type class
  IsIso (SSet.sdToNondegenerateNerve.app X)

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
example (X : SSet.{u}) [X.Nonsingular] :
    IsIso (SSet.sdToNondegenerateNerve.app X) := by
  infer_instance

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
example :
    IsIso (SSet.sdToNondegenerateNerve.app (Δ[0] : SSet.{u})) := by
  infer_instance

example {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) :
    SSet.sd.map f ≫ (SSet.sdIsoNondegenerateNerve Y).hom =
      (SSet.sdIsoNondegenerateNerve X).hom ≫
        SSet.nondegenerateNerve.map f := by
  rw [SSet.sdIsoNondegenerateNerve_hom,
    SSet.sdIsoNondegenerateNerve_hom]
  exact SSet.sdToNondegenerateNerve.naturality f

private theorem nondegenerateMap_injective
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (SSet.N.map f) := by
  intro x y hxy
  apply SSet.N.subcomplex_injective
  apply le_antisymm
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]

private noncomputable instance mono_nondegenerateNerve_map
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.nondegenerateNerve.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext
    (h := fun i => nondegenerateMap_injective f
      (congrArg (fun z => z.obj i) hab))
    (w := by
      intro i hi
      subsingleton)

example {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    Mono (SSet.sd.map f) := by
  have h :
      SSet.sd.map f ≫ (SSet.sdIsoNondegenerateNerve Y).hom =
        (SSet.sdIsoNondegenerateNerve X).hom ≫
          SSet.nondegenerateNerve.map f := by
    rw [SSet.sdIsoNondegenerateNerve_hom,
      SSet.sdIsoNondegenerateNerve_hom]
    exact SSet.sdToNondegenerateNerve.naturality f
  have : Mono ((SSet.sdIsoNondegenerateNerve X).hom ≫
      SSet.nondegenerateNerve.map f) := inferInstance
  exact mono_of_mono_fac h

example (X : SSet.{u}) [X.Nonsingular] :
    (SSet.sd.obj X).Nonsingular := by
  infer_instance

example (X : SSet.{u}) [X.Nonsingular] (k : ℕ) :
    ((SSet.sdIter k).obj X).Nonsingular := by
  infer_instance

end PublicAPI

section StandardClients

example : ((SSet.sdIter 0).obj (Δ[0] : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 1).obj (Δ[0] : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 2).obj (Δ[0] : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 0).obj (Δ[1] : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 1).obj (Δ[1] : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 2).obj (Δ[1] : SSet.{u})).Nonsingular := by
  infer_instance

/-- The union of the two faces containing vertex zero: the concrete horn
`Λ[2, 0]`, stated through public face subcomplexes to retain the sole import. -/
private def hornTwoZero : (Δ[2] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face ({0, 1} : Finset (Fin 3)) ⊔
    SSet.stdSimplex.face ({0, 2} : Finset (Fin 3))

example : (hornTwoZero : SSet.{u}).Nonsingular := by
  infer_instance

example : (SSet.sd.obj (hornTwoZero : SSet.{u})).Nonsingular := by
  infer_instance

example : ((SSet.sdIter 2).obj (hornTwoZero : SSet.{u})).Nonsingular := by
  infer_instance

end StandardClients

section NoninjectiveDegeneration

/-- The noninjective simplicial map collapsing the standard edge to a point. -/
private def collapse : (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.map (SimplexCategory.σ (n := 0) 0)

/-- The nondegenerate top edge before applying `collapse`. -/
private def topEdge : (Δ[1] : SSet.{u}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

example :
    topEdge ∈ (Δ[1] : SSet.{u}).nonDegenerate 1 :=
  SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 1

example : ¬ Function.Injective (SimplexCategory.σ (n := 0) 0) := by
  intro h
  have heq :
      (SimplexCategory.σ (n := 0) 0) (0 : Fin 2) =
        (SimplexCategory.σ (n := 0) 0) (1 : Fin 2) := by
    rfl
  have h01 : (0 : Fin 2) = 1 := h heq
  norm_num at h01

example :
    collapse.app _ topEdge ∉
      (Δ[0] : SSet.{u}).nonDegenerate 1 := by
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono]
  change ¬ Mono (SimplexCategory.σ (n := 0) 0)
  intro h
  have hinj := SimplexCategory.mono_iff_injective.mp h
  have heq :
      (SimplexCategory.σ (n := 0) 0) (0 : Fin 2) =
        (SimplexCategory.σ (n := 0) 0) (1 : Fin 2) := by
    rfl
  have h01 : (0 : Fin 2) = 1 := hinj heq
  norm_num at h01

example : (Δ[1] : SSet.{u}).N →o (Δ[0] : SSet.{u}).N :=
  SSet.N.map collapse

example :
    SSet.nondegenerateNerve.obj (Δ[1] : SSet.{u}) ⟶
      SSet.nondegenerateNerve.obj (Δ[0] : SSet.{u}) :=
  SSet.nondegenerateNerve.map collapse

example :
    SSet.sd.map collapse ≫
        SSet.sdToNondegenerateNerve.app (Δ[0] : SSet.{u}) =
      SSet.sdToNondegenerateNerve.app (Δ[1] : SSet.{u}) ≫
        SSet.nondegenerateNerve.map collapse :=
  SSet.sdToNondegenerateNerve.naturality collapse

end NoninjectiveDegeneration

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionNonsingularTests
