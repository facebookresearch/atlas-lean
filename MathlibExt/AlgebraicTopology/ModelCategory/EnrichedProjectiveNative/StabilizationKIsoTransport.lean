/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
public import MathlibExt.CategoryTheory.Enriched.Evaluation

/-!
# Transport of stabilization conditions along isomorphisms

For a labeled stabilization family in a pointed CGWH enriched functor category,
the Omega condition is invariant under enriched-functor isomorphisms.
Naturality of each stabilization adjunct gives a square whose vertical maps are
isomorphisms, so weak equivalence of the adjunct transfers in both directions.
The same condition therefore transfers objectwise along natural isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeOmegaIsoTransport

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeStabilizationFamily.{u, v} I L)

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- An actual full enriched isomorphism preserves every original stabilization transpose. -/
theorem isOmega_of_iso
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (e : X ≅ Y)
    (hX : NativeK.IsOmega s X) : NativeK.IsOmega s Y := by
  intro l
  let K := s.coefficient l
  let a := s.source l
  let b := s.target l
  let p := CurrentFree.adjoint a b K (s.inclusion l) X
  let q := CurrentFree.adjoint a b K (s.inclusion l) Y
  let f := component e.hom a
  let g := (ihom K).map (component e.hom b)
  let ea := (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) a).mapIso e
  let eb := (ihom K).mapIso
    ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b).mapIso e)
  have : IsIso f := by change IsIso ea.hom; infer_instance
  have : IsIso g := by change IsIso eb.hom; infer_instance
  have hn : f ≫ q = p ≫ g := CurrentFree.adjoint_naturality a b K (s.inclusion l) e.hom
  have hp : weakEquivalences PointedCGWH.{u, v} p := hX l
  have hf : weakEquivalences PointedCGWH.{u, v} f :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso f
  have hg : weakEquivalences PointedCGWH.{u, v} g :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso g
  have hpg := (weakEquivalences PointedCGWH.{u, v}).comp_mem p g hp hg
  have hfq : weakEquivalences PointedCGWH.{u, v} (f ≫ q) := by
    rw [hn]
    exact hpg
  exact (weakEquivalences PointedCGWH.{u, v}).of_precomp f q hf hfq

/-- Both directions retain the entire original all-label Omega predicate. -/
theorem isOmega_iff_of_iso
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (e : X ≅ Y) :
    NativeK.IsOmega s X ↔ NativeK.IsOmega s Y :=
  ⟨isOmega_of_iso s e, isOmega_of_iso s e.symm⟩

/-- An actual whole functor isomorphism transfers the original Omega condition at every input. -/
theorem isOmega_obj_of_natIso
    {C : Type*} [Category C]
    {F G : C ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I}
    (e : F ≅ G) (X : C) (hG : NativeK.IsOmega s (G.obj X)) :
    NativeK.IsOmega s (F.obj X) :=
  isOmega_of_iso s (e.app X).symm hG

end NativeOmegaRecovery.NativeOmegaIsoTransport
