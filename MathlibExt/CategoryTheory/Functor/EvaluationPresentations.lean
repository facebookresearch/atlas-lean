/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Presentations of diagrams by evaluation adjoints

Coordinate morphisms of a diagram assemble into a morphism to a product of right
adjoints, or from a coproduct of left adjoints. The adjunction triangle identities
recover each coordinate morphism. Coordinate monomorphisms and epimorphisms therefore
give monomorphisms and epimorphisms of diagrams.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Functor

open Limits

universe uI vI uC vC

variable {I : Type uI} [Category.{vI} I] {C : Type uC} [Category.{vC} C]

section Product

variable [∀ a b : I, HasProductsOfShape (a ⟶ b) C]

/-- Let `I` and `C` be categories, with products in `C` indexed by each hom-set of `I`.
For a diagram `F : I ⥤ C`, objects `A(k)` and morphisms `e(k) : F(k) → A(k)`, assume
the product in the diagram category of the evaluation right-adjoint objects `R_k(A(k))`
exists. The adjuncts of the `e(k)` assemble into a morphism `F → ∏_k R_k(A(k))`. -/
def evaluationProductMap (F : I ⥤ C) (A : I → C) (e : ∀ k, F.obj k ⟶ A k)
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (A k))] :
    F ⟶ ∏ᶜ (fun k => (evaluationRightAdjoint C k).obj (A k)) :=
  Pi.lift (fun k => (evaluationAdjunctionLeft C k).unit.app F ≫
    (evaluationRightAdjoint C k).map (e k))

/-- For categories `I`, `C` with the hom-set-indexed products needed by evaluation
right adjoints, let `F : I ⥤ C`, `A(k) ∈ C`, and `e(k) : F(k) → A(k)`. If
`P = ∏_k R_k(A(k))` exists, the assembled map followed by the projection to
`R_k(A(k))` equals the unit `F → R_k(F(k))` followed by `R_k(e(k))`. -/
@[reassoc]
theorem evaluationProductMap_π (F : I ⥤ C) (A : I → C) (e : ∀ k, F.obj k ⟶ A k)
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (A k))] (k : I) :
    evaluationProductMap F A e ≫
        Pi.π (fun k => (evaluationRightAdjoint C k).obj (A k)) k =
      (evaluationAdjunctionLeft C k).unit.app F ≫
        (evaluationRightAdjoint C k).map (e k) :=
  Pi.lift_comp_π _ k

/-- For a diagram `F : I ⥤ C` and maps `e(k) : F(k) → A(k)`, assume the evaluation
right adjoints and their product `P = ∏_k R_k(A(k))` exist. Evaluating the assembled
map `F → P` at `k`, projecting to `R_k(A(k))(k)`, and applying the evaluation
adjunction counit gives exactly `e(k)`. The categories' universes are independent. -/
@[reassoc]
theorem evaluationProductMap_recover (F : I ⥤ C) (A : I → C)
    (e : ∀ k, F.obj k ⟶ A k)
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (A k))] (k : I) :
    (evaluationProductMap F A e).app k ≫
        ((Pi.π (fun k => (evaluationRightAdjoint C k).obj (A k)) k).app k ≫
          (evaluationAdjunctionLeft C k).counit.app (A k)) =
      e k := by
  have happ : (evaluationProductMap F A e).app k ≫
      (Pi.π (fun k => (evaluationRightAdjoint C k).obj (A k)) k).app k =
      ((evaluationAdjunctionLeft C k).unit.app F).app k ≫
        ((evaluationRightAdjoint C k).map (e k)).app k := by
    have h := congrArg (fun η => η.app k) (evaluationProductMap_π F A e k)
    simpa using h
  have hnat : ((evaluationRightAdjoint C k).map (e k)).app k ≫
      (evaluationAdjunctionLeft C k).counit.app (A k) =
      (evaluationAdjunctionLeft C k).counit.app (F.obj k) ≫ e k :=
    (evaluationAdjunctionLeft C k).counit.naturality (e k)
  have htriangle : ((evaluationAdjunctionLeft C k).unit.app F).app k ≫
      (evaluationAdjunctionLeft C k).counit.app (F.obj k) = 𝟙 (F.obj k) :=
    (evaluationAdjunctionLeft C k).left_triangle_components F
  rw [← Category.assoc, happ, Category.assoc, hnat, ← Category.assoc,
    htriangle, Category.id_comp]

/-- Let `I`, `C` be categories with hom-set-indexed products in `C`, and let
`e(k) : F(k) → A(k)` be monomorphisms for a diagram `F : I ⥤ C`. If the product
of evaluation right-adjoint objects `∏_k R_k(A(k))` exists in the diagram category,
the assembled morphism from `F` to that product is a monomorphism. -/
theorem evaluationProductMap_mono (F : I ⥤ C) (A : I → C)
    (e : ∀ k, F.obj k ⟶ A k) (he : ∀ k, Mono (e k))
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (A k))] :
    Mono (evaluationProductMap F A e) := by
  let : ∀ k, Mono ((evaluationProductMap F A e).app k) := fun k => by
    let : Mono (e k) := he k
    exact mono_of_mono_fac (evaluationProductMap_recover F A e k)
  exact NatTrans.mono_of_mono_app _

/-- Suppose the evaluation right adjoints exist for categories `I`, `C`. Given
diagrams `F`, `G`, maps `e(k) : F(k) → A(k)`, `e′(k) : G(k) → B(k)`, a diagram
morphism `φ : F → G` and maps `a(k) : A(k) → B(k)`, assume
`φ(k) ≫ e′(k) = e(k) ≫ a(k)` for every `k`. If both right-adjoint products exist,
then `φ ≫ assemble(e′) = assemble(e) ≫ ∏_k R_k(a(k))`. -/
theorem evaluationProductMap_naturality {F G : I ⥤ C} {A B : I → C}
    (e : ∀ k, F.obj k ⟶ A k) (e' : ∀ k, G.obj k ⟶ B k)
    (φ : F ⟶ G) (a : ∀ k, A k ⟶ B k)
    (w : ∀ k, φ.app k ≫ e' k = e k ≫ a k)
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (A k))]
    [HasProduct (fun k => (evaluationRightAdjoint C k).obj (B k))] :
    φ ≫ evaluationProductMap G B e' =
      evaluationProductMap F A e ≫
        Limits.Pi.map (fun k => (evaluationRightAdjoint C k).map (a k)) := by
  apply Pi.hom_ext
  intro k
  have hu : φ ≫ (evaluationAdjunctionLeft C k).unit.app G =
      (evaluationAdjunctionLeft C k).unit.app F ≫
        (evaluationRightAdjoint C k).map (φ.app k) :=
    (evaluationAdjunctionLeft C k).unit.naturality φ
  calc
    (φ ≫ evaluationProductMap G B e') ≫
        Pi.π (fun k => (evaluationRightAdjoint C k).obj (B k)) k =
        φ ≫ ((evaluationAdjunctionLeft C k).unit.app G ≫
          (evaluationRightAdjoint C k).map (e' k)) := by
      rw [Category.assoc, evaluationProductMap_π]
    _ = ((evaluationAdjunctionLeft C k).unit.app F ≫
        (evaluationRightAdjoint C k).map (φ.app k)) ≫
          (evaluationRightAdjoint C k).map (e' k) := by
      rw [← Category.assoc, hu]
    _ = (evaluationAdjunctionLeft C k).unit.app F ≫
        (evaluationRightAdjoint C k).map (φ.app k ≫ e' k) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (evaluationAdjunctionLeft C k).unit.app F ≫
        (evaluationRightAdjoint C k).map (e k ≫ a k) := by rw [w k]
    _ = (evaluationProductMap F A e ≫
        Limits.Pi.map (fun k => (evaluationRightAdjoint C k).map (a k))) ≫
          Pi.π (fun k => (evaluationRightAdjoint C k).obj (B k)) k := by
      simp only [Category.assoc, Limits.Pi.map_π, evaluationProductMap_π_assoc,
        Functor.map_comp]

end Product

section Coproduct

variable [∀ a b : I, HasCoproductsOfShape (a ⟶ b) C]

/-- Let `I`, `C` be categories, with coproducts in `C` indexed by each hom-set of `I`.
For a diagram `F : I ⥤ C`, objects `A(k)` and maps `e(k) : A(k) → F(k)`, assume
the coproduct in the diagram category of the evaluation left-adjoint objects `L_k(A(k))`
exists. The adjuncts of the `e(k)` assemble into a morphism `∐_k L_k(A(k)) → F`. -/
def evaluationCoproductMap (F : I ⥤ C) (A : I → C) (e : ∀ k, A k ⟶ F.obj k)
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (A k))] :
    (∐ fun k => (evaluationLeftAdjoint C k).obj (A k)) ⟶ F :=
  Sigma.desc (fun k => (evaluationLeftAdjoint C k).map (e k) ≫
    (evaluationAdjunctionRight C k).counit.app F)

/-- For categories `I`, `C` with the hom-set-indexed coproducts needed by evaluation
left adjoints, let `F : I ⥤ C`, `A(k) ∈ C`, and `e(k) : A(k) → F(k)`. If
`S = ∐_k L_k(A(k))` exists, its inclusion of `L_k(A(k))` followed by assembly
equals `L_k(e(k))` followed by the evaluation adjunction counit `L_k(F(k)) → F`. -/
@[reassoc]
theorem evaluationCoproductMap_ι (F : I ⥤ C) (A : I → C)
    (e : ∀ k, A k ⟶ F.obj k)
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (A k))] (k : I) :
    Sigma.ι (fun k => (evaluationLeftAdjoint C k).obj (A k)) k ≫
        evaluationCoproductMap F A e =
      (evaluationLeftAdjoint C k).map (e k) ≫
        (evaluationAdjunctionRight C k).counit.app F :=
  Sigma.ι_comp_desc _ k

/-- For a diagram `F : I ⥤ C` and maps `e(k) : A(k) → F(k)`, assume the evaluation
left adjoints and the coproduct `S = ∐_k L_k(A(k))` exist. The evaluation adjunction
unit `A(k) → L_k(A(k))(k)`, followed by the coproduct inclusion evaluated at `k`
and the assembled map evaluated at `k`, gives exactly `e(k)`. -/
@[reassoc]
theorem evaluationCoproductMap_recover (F : I ⥤ C) (A : I → C)
    (e : ∀ k, A k ⟶ F.obj k)
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (A k))] (k : I) :
    ((evaluationAdjunctionRight C k).unit.app (A k) ≫
        (Sigma.ι (fun k => (evaluationLeftAdjoint C k).obj (A k)) k).app k) ≫
          (evaluationCoproductMap F A e).app k =
      e k := by
  have happ : (Sigma.ι (fun k => (evaluationLeftAdjoint C k).obj (A k)) k).app k ≫
      (evaluationCoproductMap F A e).app k =
      ((evaluationLeftAdjoint C k).map (e k)).app k ≫
        ((evaluationAdjunctionRight C k).counit.app F).app k := by
    have h := congrArg (fun η => η.app k) (evaluationCoproductMap_ι F A e k)
    simpa using h
  have hnat : (evaluationAdjunctionRight C k).unit.app (A k) ≫
      ((evaluationLeftAdjoint C k).map (e k)).app k =
      e k ≫ (evaluationAdjunctionRight C k).unit.app (F.obj k) :=
    ((evaluationAdjunctionRight C k).unit.naturality (e k)).symm
  have htriangle : (evaluationAdjunctionRight C k).unit.app (F.obj k) ≫
      ((evaluationAdjunctionRight C k).counit.app F).app k = 𝟙 (F.obj k) :=
    (evaluationAdjunctionRight C k).right_triangle_components F
  rw [Category.assoc, happ, ← Category.assoc, hnat, Category.assoc,
    htriangle, Category.comp_id]

/-- Let `I`, `C` be categories with hom-set-indexed coproducts in `C`, and let
`e(k) : A(k) → F(k)` be epimorphisms for a diagram `F : I ⥤ C`. If the coproduct
of evaluation left-adjoint objects `∐_k L_k(A(k))` exists in the diagram category,
the assembled morphism from that coproduct to `F` is an epimorphism. -/
theorem evaluationCoproductMap_epi (F : I ⥤ C) (A : I → C)
    (e : ∀ k, A k ⟶ F.obj k) (he : ∀ k, Epi (e k))
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (A k))] :
    Epi (evaluationCoproductMap F A e) := by
  let : ∀ k, Epi ((evaluationCoproductMap F A e).app k) := fun k => by
    let : Epi (e k) := he k
    exact epi_of_epi_fac (evaluationCoproductMap_recover F A e k)
  exact NatTrans.epi_of_epi_app _

/-- Suppose the evaluation left adjoints exist for categories `I`, `C`. Given
diagrams `F`, `G`, maps `e(k) : A(k) → F(k)`, `e′(k) : B(k) → G(k)`, a diagram
morphism `φ : F → G` and maps `a(k) : A(k) → B(k)`, assume
`a(k) ≫ e′(k) = e(k) ≫ φ(k)` for every `k`. If both left-adjoint coproducts exist,
then `∐_k L_k(a(k)) ≫ assemble(e′) = assemble(e) ≫ φ`. -/
theorem evaluationCoproductMap_naturality {F G : I ⥤ C} {A B : I → C}
    (e : ∀ k, A k ⟶ F.obj k) (e' : ∀ k, B k ⟶ G.obj k)
    (φ : F ⟶ G) (a : ∀ k, A k ⟶ B k)
    (w : ∀ k, a k ≫ e' k = e k ≫ φ.app k)
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (A k))]
    [HasCoproduct (fun k => (evaluationLeftAdjoint C k).obj (B k))] :
    Limits.Sigma.map (fun k => (evaluationLeftAdjoint C k).map (a k)) ≫
        evaluationCoproductMap G B e' =
      evaluationCoproductMap F A e ≫ φ := by
  apply Sigma.hom_ext
  intro k
  have hc : (evaluationLeftAdjoint C k).map (φ.app k) ≫
      (evaluationAdjunctionRight C k).counit.app G =
      (evaluationAdjunctionRight C k).counit.app F ≫ φ :=
    (evaluationAdjunctionRight C k).counit.naturality φ
  calc
    Sigma.ι (fun k => (evaluationLeftAdjoint C k).obj (A k)) k ≫
        (Limits.Sigma.map (fun k => (evaluationLeftAdjoint C k).map (a k)) ≫
          evaluationCoproductMap G B e') =
        (evaluationLeftAdjoint C k).map (a k) ≫
          ((evaluationLeftAdjoint C k).map (e' k) ≫
            (evaluationAdjunctionRight C k).counit.app G) := by
      rw [← Category.assoc, Sigma.ι_map, Category.assoc, evaluationCoproductMap_ι]
    _ = (evaluationLeftAdjoint C k).map (a k ≫ e' k) ≫
        (evaluationAdjunctionRight C k).counit.app G := by
      rw [Functor.map_comp, Category.assoc]
    _ = (evaluationLeftAdjoint C k).map (e k ≫ φ.app k) ≫
        (evaluationAdjunctionRight C k).counit.app G := by rw [w k]
    _ = (evaluationLeftAdjoint C k).map (e k) ≫
        ((evaluationAdjunctionRight C k).counit.app F ≫ φ) := by
      rw [Functor.map_comp, Category.assoc, hc]
    _ = Sigma.ι (fun k => (evaluationLeftAdjoint C k).obj (A k)) k ≫
        (evaluationCoproductMap F A e ≫ φ) :=
      (evaluationCoproductMap_ι_assoc F A e k φ).symm

end Coproduct

end CategoryTheory.Functor
