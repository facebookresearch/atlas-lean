/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Fibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Triangle
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.Triangle
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Equivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.CocartesianEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.EquivalenceReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.EquivalenceReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom

/-!
# Actual maximal parameter marking over a fixed base

A minimally parameter-marked prism into an intrinsically Cartesian or
cocartesian marked total space preserves the maximal parameter marking
exactly when its vertical original edges are equivalences. The base map is
the supplied map from the source, independent of the parameter. The two
mixed product triangles prove the converse with their entire original
two-simplices. The parameter and source need not be quasicategories.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem vertical_base_degenerate {T : SSet.{u}} {X : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) (r : X.toSSet ⟶ B) (f : T ⊗ X.toSSet ⟶ E)
    (hf : f ≫ p = CartesianMonoidalCategory.snd T X.toSSet ≫ r)
    (a : T _⦋1⦌) (x : X.toSSet _⦋0⦌) :
    ((Edge.mk' (f.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x))).map p).IsEquivalence := by
  let z : (T ⊗ X.toSSet) _⦋1⦌ := (a, X.toSSet.σ (0 : Fin 1) x)
  have h := ConcreteCategory.congr_hom (congr_app hf (op ⦋1⦌)) z
  change p.app (op ⦋1⦌) (f.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x)) =
    r.app (op ⦋1⦌) (X.toSSet.σ (0 : Fin 1) x) at h
  have h' : p.app (op ⦋1⦌) (f.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x)) =
      B.σ (0 : Fin 1) (r.app (op ⦋0⦌) x) :=
    h.trans (SSet.σ_naturality_apply r (0 : Fin 1) x)
  exact (Edge.isEquivalence_id (r.app (op ⦋0⦌) x)).of_edge_eq h'.symm

/-- Maximal parameter marking for an actual fixed-base Cartesian prism is detected by its vertical edges. -/
theorem preserves_maxParameter_cartesian_iff {T : SSet.{u}} {X : Marked.{u}}
    {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (r : X.toSSet ⟶ B) (f : prod (min T) X ⟶ cartesian p)
    (hf : f.hom ≫ p = CartesianMonoidalCategory.snd T X.toSSet ≫ r) :
    (∀ (e : (prod (max T) X).toSSet _⦋1⦌),
      e ∈ (prod (max T) X).marking → f.hom.app (op ⦋1⦌) e ∈ (cartesian p).marking) ↔
    ∀ (a : T _⦋1⦌) (x : X.toSSet _⦋0⦌),
      (Edge.mk' (f.hom.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x))).IsEquivalence := by
  constructor
  · intro h a x
    let e := Edge.mk' (f.hom.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x))
    exact CartesianEdge.isEquivalence_of_map p e
      (h (a, X.toSSet.σ (0 : Fin 1) x) ⟨Set.mem_univ _, X.degenerate_mem x⟩)
      (vertical_base_degenerate p r f.hom hf a x)
  · intro h e he
    let z : (T ⊗ X.toSSet) _⦋1⦌ := e
    let F : T ⊗ X.toSSet ⟶ E := f.hom
    let a : Edge (T.δ 1 z.1) (T.δ 0 z.1) := Edge.mk' z.1
    let b : Edge (X.toSSet.δ 1 z.2) (X.toSSet.δ 0 z.2) := Edge.mk' z.2
    let v := (a.tensor (Edge.id (X.toSSet.δ 1 z.2))).map F
    let w := ((Edge.id (T.δ 0 z.1)).tensor b).map F
    have hve : v.IsEquivalence := (h z.1 (X.toSSet.δ 1 z.2)).of_edge_eq rfl
    have hv : CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm v.edge) :=
      CartesianEdge.isPCartesian_of_isEquivalence p _
        (hve.of_edge_eq (Equiv.apply_symm_apply SSet.yonedaEquiv v.edge).symm)
    let z' : (prod (min T) X).toSSet _⦋1⦌ := (T.σ (0 : Fin 1) (T.δ 0 z.1), z.2)
    have hz' : z' ∈ (prod (min T) X).marking := ⟨⟨T.δ 0 z.1, rfl⟩, he.2⟩
    have hw : CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm w.edge) :=
      @f.preserve z' hz'
    let d := (a.tensor b).map F
    have H : Edge.CompStruct v w d :=
      ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
    have hd : CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm d.edge) :=
      CartesianEdge.isPCartesian_of_compStruct (e₀₁ := v) (e₁₂ := w) (e₀₂ := d) p H hv hw
    exact hd

/-- Maximal parameter marking for a fixed-base cocartesian prism has the same vertical-equivalence criterion. -/
theorem preserves_maxParameter_cocartesian_iff {T : SSet.{u}} {X : Marked.{u}}
    {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (r : X.toSSet ⟶ B) (f : prod (min T) X ⟶ cocartesian p)
    (hf : f.hom ≫ p = CartesianMonoidalCategory.snd T X.toSSet ≫ r) :
    (∀ (e : (prod (max T) X).toSSet _⦋1⦌),
      e ∈ (prod (max T) X).marking → f.hom.app (op ⦋1⦌) e ∈ (cocartesian p).marking) ↔
    ∀ (a : T _⦋1⦌) (x : X.toSSet _⦋0⦌),
      (Edge.mk' (f.hom.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x))).IsEquivalence := by
  constructor
  · intro h a x
    let e := Edge.mk' (f.hom.app (op ⦋1⦌) (a, X.toSSet.σ (0 : Fin 1) x))
    exact CocartesianEdge.isEquivalence_of_map p e
      (h (a, X.toSSet.σ (0 : Fin 1) x) ⟨Set.mem_univ _, X.degenerate_mem x⟩)
      (vertical_base_degenerate p r f.hom hf a x)
  · intro h e he
    let z : (T ⊗ X.toSSet) _⦋1⦌ := e
    let F : T ⊗ X.toSSet ⟶ E := f.hom
    let a : Edge (T.δ 1 z.1) (T.δ 0 z.1) := Edge.mk' z.1
    let b : Edge (X.toSSet.δ 1 z.2) (X.toSSet.δ 0 z.2) := Edge.mk' z.2
    let v := ((Edge.id (T.δ 1 z.1)).tensor b).map F
    let w := (a.tensor (Edge.id (X.toSSet.δ 0 z.2))).map F
    let z' : (prod (min T) X).toSSet _⦋1⦌ := (T.σ (0 : Fin 1) (T.δ 1 z.1), z.2)
    have hz' : z' ∈ (prod (min T) X).marking := ⟨⟨T.δ 1 z.1, rfl⟩, he.2⟩
    have hv : CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm v.edge) :=
      @f.preserve z' hz'
    have hwe : w.IsEquivalence := (h z.1 (X.toSSet.δ 0 z.2)).of_edge_eq rfl
    have hw : CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm w.edge) :=
      CocartesianEdge.isPCocartesian_of_isEquivalence p _
        (hwe.of_edge_eq (Equiv.apply_symm_apply SSet.yonedaEquiv w.edge).symm)
    let d := (a.tensor b).map F
    have H : Edge.CompStruct v w d :=
      ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map F
    have hd : CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm d.edge) :=
      CocartesianEdge.isPCocartesian_of_compStruct (e₀₁ := v) (e₁₂ := w) (e₀₂ := d) p H hv hw
    exact hd

end SSet.Marked
