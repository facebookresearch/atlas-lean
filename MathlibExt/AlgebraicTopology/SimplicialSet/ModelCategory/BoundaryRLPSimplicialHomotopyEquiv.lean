/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomZero
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Boundary lifting gives realized weak equivalences

Let p:E→B in simplicial-set universe u lift against every boundary inclusion ∂Δ[n]→Δ[n], n≥0.
There is a section s:B→E with s≫p=id_B and a simplicial homotopy p≫s≃id_E. Realization therefore
sends p to a weak homotopy equivalence of spaces.

The homotopy is obtained by lifting the cylinder boundary E⊗∂Δ[1]→E⊗Δ[1] with the prescribed two
endpoint maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

/-!
## The two endpoint maps

Two maps f₀,f₁:E→E determine a map E⊗∂Δ[1]→E. The face δ₁, which is geometric endpoint 0, gives
f₀, while δ₀, geometric endpoint 1, gives f₁. Their intersection is empty, so the pair is glued
by the boundary coproduct presentation.
-/

private lemma boundaryOneMulticoequalizerDiagram :
    Subcomplex.MulticoequalizerDiagram (boundary.{u} 1)
      (fun j : Fin 2 ↦ stdSimplex.face {j}ᶜ)
      (fun j k : Fin 2 ↦ stdSimplex.face {j, k}ᶜ) where
  iSup_eq := by rw [boundary_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

private noncomputable def boundaryOneIsColimit :
    IsColimit (boundaryOneMulticoequalizerDiagram.multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  boundaryOneMulticoequalizerDiagram.isColimit'

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def boundaryOneMulticofork {X : SSet.{u}}
    (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) :
    Multicofork (boundaryOneMulticoequalizerDiagram.multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X
    (fun j ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ faces j) (by
      rintro ⟨⟨a, b⟩, hab⟩
      dsimp at hab ⊢
      fin_cases a <;> fin_cases b
      all_goals simp at hab
      have hbot :
          (stdSimplex.face ({0, 1} : Finset (Fin 2))ᶜ :
            (Δ[1] : SSet.{u}).Subcomplex) = ⊥ := by
        rw [show ({0, 1} : Finset (Fin 2))ᶜ = ∅ by decide,
          stdSimplex.face_empty]
      exact ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso hbot).symm).hom_ext _ _)

private noncomputable def boundaryOneDesc {X : SSet.{u}}
    (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) :
    (boundary 1 : SSet.{u}) ⟶ X :=
  boundaryOneIsColimit.desc (boundaryOneMulticofork faces)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma boundary_ι_boundaryOneDesc {X : SSet.{u}}
    (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) (j : Fin 2) :
    boundary.ι j ≫ boundaryOneDesc faces = faces j := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).inv]
  rw [← Category.assoc, boundary.faceSingletonComplIso_inv_ι]
  simpa [boundaryOneDesc, boundaryOneMulticofork, boundary.faceι] using!
    boundaryOneIsColimit.fac (boundaryOneMulticofork faces) (.right j)

private noncomputable def endpointMap {E : SSet.{u}} (f₀ f₁ : E ⟶ E) :
    E ⊗ (boundary 1 : SSet.{u}) ⟶ E :=
  uncurry (boundaryOneDesc (fun j ↦
    yonedaEquiv.symm ((ihom₀Equiv E E).symm (if j = 1 then f₀ else f₁))))

private lemma whiskerLeft_boundary_ι_endpointMap {E : SSet.{u}}
    (f₀ f₁ : E ⟶ E) (j : Fin 2) :
    (E ◁ boundary.ι j) ≫ endpointMap f₀ f₁ =
      (stdSimplex.rightUnitor E).hom ≫ (if j = 1 then f₀ else f₁) := by
  dsimp [endpointMap]
  rw [← MonoidalClosed.uncurry_natural_left]
  rw [boundary_ι_boundaryOneDesc]
  let f : E ⟶ E := if j = 1 then f₀ else f₁
  apply (cancel_epi (stdSimplex.rightUnitor E).inv).mp
  simp

/-!
## The section and homotopy inverse

Boundary lifting first gives a strict section s of p, then fills the cylinder with endpoints p≫s
and id_E. Thus ι₀≫H=p≫s and ι₁≫H=id_E for H:E⊗Δ[1]→E.
-/

private theorem exists_homotopyInverse_of_rlp_I {E B : SSet.{u}}
    {p : E ⟶ B} (hp : modelCategoryQuillen.I.{u}.rlp p) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B ∧
      Nonempty (SSet.Homotopy (p ≫ s) (𝟙 E)) := by
  have hpMono : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
    rw [SSet.rlp_monomorphisms]
    exact hp
  let botB : B.Subcomplex := ⊥
  let top₀ : (botB : SSet.{u}) ⟶ E := Subcomplex.isInitialBot.to E
  let sectionSq : CommSq top₀ botB.ι p (𝟙 B) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have hsection : HasLiftingProperty botB.ι p :=
    hpMono _ (by infer_instance)
  let s : B ⟶ E := sectionSq.lift
  have hs : s ≫ p = 𝟙 B := sectionSq.fac_right
  let k : E ⊗ (boundary 1 : SSet.{u}) ⟶ E := endpointMap (p ≫ s) (𝟙 E)
  let i : E ⊗ (boundary 1 : SSet.{u}) ⟶ E ⊗ Δ[1] :=
    E ◁ (boundary 1).ι
  have hi : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    rintro ⟨x, t⟩ ⟨y, v⟩ h
    change (x, t.1) = (y, v.1) at h
    have hxy : x = y := congrArg
      (fun z : E.obj n × (Δ[1] : SSet.{u}).obj n ↦ z.1) h
    have htv : t.1 = v.1 := congrArg
      (fun z : E.obj n × (Δ[1] : SSet.{u}).obj n ↦ z.2) h
    exact Prod.ext hxy (Subtype.ext htv)
  have hcomm : k ≫ p = i ≫ (fst E (Δ[1] : SSet.{u}) ≫ p) := by
    apply MonoidalClosed.curry_injective
    apply boundary.hom_ext
    intro j
    rw [← MonoidalClosed.curry_natural_left,
      ← MonoidalClosed.curry_natural_left]
    apply congrArg MonoidalClosed.curry
    calc
      (E ◁ boundary.ι j) ≫ (k ≫ p) =
          ((E ◁ boundary.ι j) ≫ k) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = ((stdSimplex.rightUnitor E).hom ≫
          (if j = 1 then p ≫ s else 𝟙 E)) ≫ p := by
        rw [whiskerLeft_boundary_ι_endpointMap]
      _ = (stdSimplex.rightUnitor E).hom ≫ p := by
        fin_cases j <;> simp [hs, Category.assoc]
      _ = (E ◁ boundary.ι j) ≫
          (i ≫ (fst E (Δ[1] : SSet.{u}) ≫ p)) := by
        dsimp [i]
        rw [← Category.assoc, ← Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp,
          boundary.ι_ι, CartesianMonoidalCategory.whiskerLeft_fst]
        rfl
  let cylinderSq : CommSq k i p (fst E (Δ[1] : SSet.{u}) ≫ p) := ⟨hcomm⟩
  have hcylinder : HasLiftingProperty i p := hpMono _ (by infer_instance)
  let Hmap : E ⊗ Δ[1] ⟶ E := cylinderSq.lift
  have hHboundary : i ≫ Hmap = k := cylinderSq.fac_left
  have hboundaryComp (j : Fin 2) :
      (E ◁ boundary.ι j) ≫ i = E ◁ stdSimplex.δ j := by
    dsimp [i]
    rw [← MonoidalCategory.whiskerLeft_comp, boundary.ι_ι]
  have hzero : SSet.ι₀ ≫ Hmap = p ≫ s := by
    calc
      SSet.ι₀ ≫ Hmap =
          ((stdSimplex.rightUnitor E).inv ≫
            (E ◁ stdSimplex.δ (1 : Fin 2))) ≫ Hmap := by
        rw [stdSimplex.rightUnitor_inv_map_δ_one]
      _ = (stdSimplex.rightUnitor E).inv ≫
          ((E ◁ boundary.ι (1 : Fin 2)) ≫ i) ≫ Hmap := by
        simp only [Category.assoc, hboundaryComp]
      _ = (stdSimplex.rightUnitor E).inv ≫
          (E ◁ boundary.ι (1 : Fin 2)) ≫ (i ≫ Hmap) := by
        simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor E).inv ≫
          (E ◁ boundary.ι (1 : Fin 2)) ≫ k := by rw [hHboundary]
      _ = (stdSimplex.rightUnitor E).inv ≫
          ((stdSimplex.rightUnitor E).hom ≫ (p ≫ s)) := by
        rw [whiskerLeft_boundary_ι_endpointMap]
        simp
      _ = p ≫ s := by simp
  have hone : SSet.ι₁ ≫ Hmap = 𝟙 E := by
    calc
      SSet.ι₁ ≫ Hmap =
          ((stdSimplex.rightUnitor E).inv ≫
            (E ◁ stdSimplex.δ (0 : Fin 2))) ≫ Hmap := by
        rw [stdSimplex.rightUnitor_inv_map_δ_zero]
      _ = (stdSimplex.rightUnitor E).inv ≫
          ((E ◁ boundary.ι (0 : Fin 2)) ≫ i) ≫ Hmap := by
        simp only [Category.assoc, hboundaryComp]
      _ = (stdSimplex.rightUnitor E).inv ≫
          (E ◁ boundary.ι (0 : Fin 2)) ≫ (i ≫ Hmap) := by
        simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor E).inv ≫
          (E ◁ boundary.ι (0 : Fin 2)) ≫ k := by rw [hHboundary]
      _ = (stdSimplex.rightUnitor E).inv ≫
          ((stdSimplex.rightUnitor E).hom ≫ (𝟙 E)) := by
        rw [whiskerLeft_boundary_ι_endpointMap]
        simp
      _ = 𝟙 E := by simp
  refine ⟨s, hs, ⟨?_⟩⟩
  exact
    { h := Hmap
      h₀ := hzero
      h₁ := hone
      rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }

namespace modelCategoryQuillen

/-- In every universe u, any simplicial map p:E→B with the right lifting property against all
∂Δ[n]→Δ[n], n≥0, has |p|:|E|→|B| a weak homotopy equivalence. The lifting construction yields
s:B→E with s≫p=id_B and a simplicial homotopy p≫s≃id_E. -/
theorem I_rlp_le_realizationWeakEquivalences :
    I.{u}.rlp ≤ SSet.realizationWeakEquivalences.{u} := by
  intro E B p hp
  obtain ⟨s, hs, ⟨Hleft⟩⟩ := exists_homotopyInverse_of_rlp_I hp
  let Hright : SSet.Homotopy (s ≫ p) (𝟙 B) :=
    SSet.RelativeMorphism.Homotopy.ofEq
      (congrArg (fun f : B ⟶ B ↦ SSet.RelativeMorphism.botEquiv.symm f) hs)
  let e := SSet.realizedHomotopyEquiv E B p s Hleft Hright
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
  apply TopCat.mem_of_eq_toFun e
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrFun (SSet.coe_realizedHomotopyEquiv E B p s Hleft Hright).symm x

end modelCategoryQuillen

end SSet
