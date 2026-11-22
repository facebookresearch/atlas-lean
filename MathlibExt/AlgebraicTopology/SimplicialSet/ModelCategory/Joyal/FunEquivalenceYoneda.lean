/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy

/-!
# Yoneda upgrade: maps in `W` induce equivalences of functor quasicategories

For a probe quasicategory `D`, the swap isomorphism identifies
`h Fun(D, F)` with `h Fun(f, Fun(D, C))`, which is an equivalence by
the defining property of `W` applied at `E = Fun(D, C)` (a
quasicategory by the Joyal exponential theorem — the upstream
instance `Quasicategory ((ihom A).obj X)` in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`,
proved there by the inner-pairing argument; no wrapper is needed).
The Yoneda extraction (Kerodon 4.5.1.22 `(5)⟹(1)`, Tag `032X`)
then runs exactly as in
`SSet.categoricalEquivalences.hasHoInverse`: essential
surjectivity at the `D = Fun(X, C)` probe on the identity produces
`G` and one triangle, and reflection along the equivalence at the
`D = Fun(Y, C)` probe (`Functor.preimageIso`) produces the other.

Note on the design doc: the doc routes through `π₀`-bijections on
cores (Kerodon's condition (5)); we keep the stronger `h`-equivalences
that the `hFun`-definition of `W` gives directly and run the
`hasHoInverse` Yoneda pattern at shifted test objects, avoiding
`π₀` entirely.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

/-! ## §1. The exponential-law swap isomorphism

For a fixed probe `D` and target `C`, the swap isomorphism
`Fun(D, Fun(Y, C)) ≅ Fun(Y, Fun(D, C))` rearranges currying so that
postcomposition with `Fun(f, C)` becomes precomposition with `f`.
-/

/-- The doubly-uncurried form of the swap map: reassociate, swap the
tensor factors, then evaluate twice. -/
def ihomSwapUncurried (D Y C : SSet.{u}) :
    D ⊗ (Y ⊗ (ihom D).obj ((ihom Y).obj C)) ⟶ C :=
  (α_ D Y _).inv ≫ ((β_ D Y).hom ▷ _) ≫ (α_ Y D _).hom ≫
    (Y ◁ uncurry (𝟙 _)) ≫ uncurry (𝟙 _)

/-- The exponential-law swap map
`Fun(D, Fun(Y, C)) ⟶ Fun(Y, Fun(D, C))`. -/
def ihomSwapHom (D Y C : SSet.{u}) :
    (ihom D).obj ((ihom Y).obj C) ⟶ (ihom Y).obj ((ihom D).obj C) :=
  curry (curry (ihomSwapUncurried D Y C))

/-- Single uncurrying of the swap map. -/
private theorem uncurry_ihomSwapHom (D Y C : SSet.{u}) :
    uncurry (ihomSwapHom D Y C) = curry (ihomSwapUncurried D Y C) := by
  unfold ihomSwapHom
  rw [uncurry_curry]

/-- The swap maps in opposite directions are mutually inverse (one
triangle; the other is the same statement with `D` and `Y`
exchanged). The proof uncurries twice and computes: associator
naturality moves the whiskered swap past the reassociation,
`whisker_exchange` moves it past the braiding, the two
evaluation/curry triangles (`whiskerLeft_curry_ihom_ev_app`)
consume the swap, and the braidings cancel by symmetry. -/
theorem ihomSwapHom_comp (D Y C : SSet.{u}) :
    ihomSwapHom D Y C ≫ ihomSwapHom Y D C = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_ihomSwapHom, uncurry_id_eq_ev]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_eq]
  unfold ihomSwapHom ihomSwapUncurried
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc]
  simp only [uncurry_id_eq_ev]
  rw [whiskerLeft_curry_ihom_ev_app, whiskerLeft_curry_ihom_ev_app,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id_assoc]

/-- The exponential-law swap isomorphism
`Fun(D, Fun(Y, C)) ≅ Fun(Y, Fun(D, C))`. -/
def ihomSwap (D Y C : SSet.{u}) :
    (ihom D).obj ((ihom Y).obj C) ≅ (ihom Y).obj ((ihom D).obj C) where
  hom := ihomSwapHom D Y C
  inv := ihomSwapHom Y D C
  hom_inv_id := ihomSwapHom_comp D Y C
  inv_hom_id := ihomSwapHom_comp Y D C

/-- Naturality of the swap map: postcomposition with `Fun(f, C)`
becomes precomposition with `f` under the swap. Both sides are
uncurried twice; the left side reduces by associator/whisker
naturality, `ev`-naturality, and the `pre`/uncurry law
(`uncurry_pre`), while the right side reduces by the same plus
braiding naturality. -/
theorem ihomSwapHom_natural {X Y : SSet.{u}} (D C : SSet.{u}) (f : X ⟶ Y) :
    (ihom D).map ((pre f).app C) ≫ ihomSwapHom D X C =
      ihomSwapHom D Y C ≫ (pre f).app ((ihom D).obj C) := by
  have hL : D ◁ (X ◁ (ihom D).map ((pre f).app C)) ≫
      ihomSwapUncurried D X C =
      (α_ D X ((ihom D).obj ((ihom Y).obj C))).inv ≫
        (((β_ D X).hom ▷ (ihom D).obj ((ihom Y).obj C)) ≫
          ((α_ X D ((ihom D).obj ((ihom Y).obj C))).hom ≫
            ((X ◁ (ihom.ev D).app ((ihom Y).obj C)) ≫
              ((f ▷ (ihom Y).obj C) ≫ (ihom.ev Y).app C)))) := by
    unfold ihomSwapUncurried
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc, ← whiskerLeft_comp_assoc]
    simp only [uncurry_id_eq_ev]
    rw [ihom.ev_naturality, whiskerLeft_comp, Category.assoc,
      id_tensor_pre_app_comp_ev]
  have hR : D ◁ (f ▷ (ihom D).obj ((ihom Y).obj C)) ≫
      ihomSwapUncurried D Y C =
      (α_ D X ((ihom D).obj ((ihom Y).obj C))).inv ≫
        (((β_ D X).hom ▷ (ihom D).obj ((ihom Y).obj C)) ≫
          ((α_ X D ((ihom D).obj ((ihom Y).obj C))).hom ≫
            ((X ◁ (ihom.ev D).app ((ihom Y).obj C)) ≫
              ((f ▷ (ihom Y).obj C) ≫ (ihom.ev Y).app C)))) := by
    unfold ihomSwapUncurried
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
      associator_naturality_left_assoc]
    simp only [uncurry_id_eq_ev]
    rw [← whisker_exchange_assoc]
  apply uncurry_injective
  conv_lhs => rw [uncurry_natural_left, uncurry_ihomSwapHom]
  conv_rhs => rw [uncurry_pre_app, uncurry_ihomSwapHom]
  apply uncurry_injective
  conv_lhs => rw [uncurry_natural_left, uncurry_curry]
  conv_rhs => rw [uncurry_natural_left, uncurry_curry]
  rw [hL, hR]

/-! ## §2. The defining property of `W`, shifted across the swap

For `f ∈ W`, `h Fun(D, Fun(f, C))` is an equivalence for every probe
`D` (no quasicategory hypothesis on `D` is needed: `E = Fun(D, C)`
is a quasicategory for arbitrary `D` by the Joyal exponential
theorem): it is the composite of the swap equivalences with the
defining `h`-equivalence at `E`.
-/

/-- `hoFunctor.map` of an isomorphism of simplicial sets is an
equivalence of homotopy categories. -/
private theorem isEquivalence_hoFunctor_map_of_isIso {P Q : SSet.{u}}
    (e : P ≅ Q) :
    (hoFunctor.map e.hom).toFunctor.IsEquivalence := by
  have e1 : (𝟭 (hoFunctor.obj P)) =
      (hoFunctor.map e.hom).toFunctor ⋙
        (hoFunctor.map e.inv).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← hoFunctor.map_comp, Iso.hom_inv_id,
      hoFunctor.map_id, Cat.Hom.id_toFunctor]
  have e2 : (hoFunctor.map e.inv).toFunctor ⋙
        (hoFunctor.map e.hom).toFunctor =
      𝟭 (hoFunctor.obj Q) := by
    rw [← Cat.Hom.comp_toFunctor, ← hoFunctor.map_comp, Iso.inv_hom_id,
      hoFunctor.map_id, Cat.Hom.id_toFunctor]
  exact Functor.IsEquivalence.mk' _ (eqToIso e1) (eqToIso e2)

/-- For `f ∈ W` and a quasicategory `C`, `h Fun(D, Fun(f, C))` is an
equivalence for every probe `D`: the defining `h`-equivalence at
`E = Fun(D, C)` (a quasicategory for arbitrary `D` by the Joyal
exponential theorem, upstream) transported across the swap. -/
theorem categoricalEquivalences.isEquivalence_hoFun_probe {X Y : SSet.{u}}
    {f : X ⟶ Y} (hf : categoricalEquivalences f) (C : SSet.{u})
    [Quasicategory C] (D : SSet.{u}) :
    (hoFunctor.map ((ihom D).map ((pre f).app C))).toFunctor.IsEquivalence := by
  have hE : Quasicategory ((ihom D).obj C) := inferInstance
  have hmid : (hoFunctor.map
      ((pre f).app ((ihom D).obj C))).toFunctor.IsEquivalence :=
    hf _ hE
  have hY : (hoFunctor.map
      (ihomSwap D Y C).hom).toFunctor.IsEquivalence :=
    isEquivalence_hoFunctor_map_of_isIso (ihomSwap D Y C)
  have hX : (hoFunctor.map
      (ihomSwap D X C).inv).toFunctor.IsEquivalence :=
    isEquivalence_hoFunctor_map_of_isIso (ihomSwap D X C).symm
  have hsq : (ihom D).map ((pre f).app C) ≫ (ihomSwap D X C).hom =
      (ihomSwap D Y C).hom ≫ (pre f).app ((ihom D).obj C) :=
    ihomSwapHom_natural (D := D) (C := C) f
  have hfactor : (ihom D).map ((pre f).app C) =
      (ihomSwap D Y C).hom ≫ (pre f).app ((ihom D).obj C) ≫
        (ihomSwap D X C).inv := by
    have h1 : (ihom D).map ((pre f).app C) =
        ((ihom D).map ((pre f).app C) ≫ (ihomSwap D X C).hom) ≫
          (ihomSwap D X C).inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : ((ihom D).map ((pre f).app C) ≫ (ihomSwap D X C).hom) ≫
          (ihomSwap D X C).inv =
        (ihomSwap D Y C).hom ≫ (pre f).app ((ihom D).obj C) ≫
          (ihomSwap D X C).inv := by
      rw [hsq, Category.assoc]
    exact h1.trans h2
  rw [hfactor, hoFunctor.map_comp, hoFunctor.map_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom.comp_toFunctor]
  infer_instance

/-! ## §3. The Yoneda upgrade (Y0 proper, Kerodon 4.5.4.8 / Tag `01EF`)

Probing with `D = Fun(X, C)` and `D = Fun(Y, C)` and running the
`hasHoInverse` Yoneda pattern (essential surjectivity +
`Functor.preimageIso`, as in Kerodon 4.5.1.22 `(5)⟹(1)` / Tag `032X`).
-/

/-- Every object of `h Fun(Z, C)` is the vertex classified by a map
`Z ⟶ C`. (Same proof as the private lemma of `DwyerKan.lean`.) -/
private theorem exists_eq_mk_ihomVertexEquiv {Z C : SSet.{u}}
    (a : ((ihom Z).obj C).HomotopyCategory) :
    ∃ m : Z ⟶ C, a = HomotopyCategory.mk (ihomVertexEquiv Z C m) := by
  refine ⟨(ihomVertexEquiv Z C).symm (HomotopyCategory.objEquiv a), ?_⟩
  rw [Equiv.apply_symm_apply]
  exact (HomotopyCategory.objEquiv.left_inv a).symm

/-- Precomposition on `h Fun` sends the vertex classified by `m` to the
vertex classified by `f ≫ m`. (Same proof as in `DwyerKan.lean`.) -/
private theorem hoPre_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (f : A ⟶ B)
    (m : B ⟶ C) :
    (hoFunctor.map ((pre f).app C)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv B C m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (f ≫ m)) := by
  change (mapHomotopyCategory ((pre f).app C)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_pre_app]

/-- Postcomposition on `h Fun` sends the vertex classified by `m` to
the vertex classified by `m ≫ q`. (Same proof as in
`DwyerKan.lean`.) -/
private theorem hoPost_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (m : A ⟶ B)
    (q : B ⟶ C) :
    (hoFunctor.map ((ihom A).map q)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv A B m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (m ≫ q)) := by
  change (mapHomotopyCategory ((ihom A).map q)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_ihom_map]

/-- **Yoneda upgrade (Y0, Kerodon 4.5.4.8, Tag `01EF`)**: if `f ∈ W`
then `Fun(f, C)` is an equivalence of quasicategories for every
quasicategory `C`, in Stevenson's sense (`SSet.HasHoInverse`).
Essential surjectivity of the `D = Fun(X, C)` probe at the identity
produces `G` and the second triangle; reflection along the
`D = Fun(Y, C)` probe equivalence (`Functor.preimageIso`) produces
the first. -/
theorem categoricalEquivalences.functorEquivalence_of_mem {X Y : SSet.{u}}
    {f : X ⟶ Y} (hf : categoricalEquivalences f) (C : SSet.{u})
    [Quasicategory C] : HasHoInverse ((pre f).app C) := by
  have hA : Quasicategory ((ihom Y).obj C) := inferInstance
  have hB : Quasicategory ((ihom X).obj C) := inferInstance
  have hProbeB : (hoFunctor.map
      ((ihom ((ihom X).obj C)).map ((pre f).app C))).toFunctor.IsEquivalence :=
    hf.isEquivalence_hoFun_probe C ((ihom X).obj C)
  have hProbeA : (hoFunctor.map
      ((ihom ((ihom Y).obj C)).map ((pre f).app C))).toFunctor.IsEquivalence :=
    hf.isEquivalence_hoFun_probe C ((ihom Y).obj C)
  obtain ⟨a, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage
    (hoFunctor.map
      ((ihom ((ihom X).obj C)).map ((pre f).app C))).toFunctor
    (HomotopyCategory.mk (ihomVertexEquiv _ _ (𝟙 ((ihom X).obj C))))
  obtain ⟨G, rfl⟩ := exists_eq_mk_ihomVertexEquiv a
  rw [hoPost_obj_mk_ihomVertexEquiv] at α
  have hpost : (HomotopyCategory.mk
        (ihomVertexEquiv _ _ (((pre f).app C ≫ G) ≫ (pre f).app C)) :
        hoFunctor.obj ((ihom ((ihom Y).obj C)).obj ((ihom X).obj C))) ≅
      HomotopyCategory.mk (ihomVertexEquiv _ _ ((pre f).app C)) := by
    have h := (hoFunctor.map
      ((pre ((pre f).app C)).app ((ihom X).obj C))).toFunctor.mapIso α
    rw [hoPre_obj_mk_ihomVertexEquiv, hoPre_obj_mk_ihomVertexEquiv] at h
    rwa [Category.comp_id, ← Category.assoc] at h
  have hpre : (hoFunctor.map
        ((ihom ((ihom Y).obj C)).map ((pre f).app C))).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv _ _ ((pre f).app C ≫ G))) ≅
      (hoFunctor.map
        ((ihom ((ihom Y).obj C)).map ((pre f).app C))).toFunctor.obj
        (HomotopyCategory.mk
          (ihomVertexEquiv _ _ (𝟙 ((ihom Y).obj C)))) := by
    rw [hoPost_obj_mk_ihomVertexEquiv, hoPost_obj_mk_ihomVertexEquiv,
      Category.id_comp]
    exact hpost
  exact ⟨G, ⟨(hoFunctor.map
    ((ihom ((ihom Y).obj C)).map ((pre f).app C))).toFunctor.preimageIso
      hpre⟩, ⟨α⟩⟩

/-! ## §4. Equivalences induce weak equivalences on cores

From `HasHoInverse` data, the two triangles are equivalence edges of
functor quasicategories; uncurrying an equivalence edge and lifting to
cores gives the simplicial homotopies exhibiting
`SSet.core.map F` as a homotopy equivalence, hence
`SSet.KanComplex.W` by `SSet.KanComplex.W.of_homotopy`.
-/

/-- Evaluation at a vertex as a simplicial map `Fun(A, A) ⟶ A`
(proof-only helper for the core-direction homotopies below). -/
private def evAtVertex {A : SSet.{u}} (w : A _⦋0⦌) :
    (ihom A).obj A ⟶ A :=
  (λ_ _).inv ≫ ((unitHomEquiv A).symm w ▷ _) ≫ (ihom.ev A).app A

/-- The curried name of a vertex evaluates on `1`-simplices to the
degenerate edge: the unit map is constant. -/
private theorem unitHomEquiv_symm_app_one {A : SSet.{u}} (w : A _⦋0⦌)
    (s : (𝟙_ SSet.{u}) _⦋1⦌) :
    ((unitHomEquiv A).symm w).app (op ⦋1⦌) s = (Edge.id w).edge := by
  have hmap : ((unitHomEquiv A).symm w).app (op ⦋1⦌) s =
      A.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op w := rfl
  rw [hmap, ← SimplexCategory.eq_const_to_zero (SimplexCategory.σ 0),
    Edge.id_edge]
  rfl

/-- Evaluation at a vertex is evaluation of a degenerate edge in the
first factor: the `1`-simplex β-rule for `SSet.evAtVertex`. -/
private theorem evAtVertex_app_one {A : SSet.{u}} (w : A _⦋0⦌)
    (t : ((ihom A).obj A) _⦋1⦌) :
    (evAtVertex w).app (op ⦋1⦌) t =
      ((ihom.ev A).app A).app (op ⦋1⦌) ((Edge.id w).edge, t) := by
  have h1 : ((λ_ ((ihom A).obj A)).inv).app (op ⦋1⦌) t = (PUnit.unit, t) :=
    leftUnitor_inv_app_apply _ _
  have h2 : (((unitHomEquiv A).symm w ▷ (ihom A).obj A)).app (op ⦋1⦌)
        (PUnit.unit, t) =
      (((unitHomEquiv A).symm w).app (op ⦋1⦌) PUnit.unit, t) :=
    whiskerRight_app_apply _ _ _
  change (((λ_ ((ihom A).obj A)).inv ≫
      (((unitHomEquiv A).symm w ▷ (ihom A).obj A)) ≫
      (ihom.ev A).app A).app (op ⦋1⦌) t) = _
  rw [NatTrans.comp_app, NatTrans.comp_app, types_comp_apply,
    types_comp_apply, h1, h2, unitHomEquiv_symm_app_one]

/-- The naturality prism: evaluation sends a tensor edge of
equivalences to an equivalence. The tensor edge factors as
`(α ⊗ id) ≫ (id ⊗ Φ)`; the factors agree (as `1`-simplices) with
`α.map _` and `Φ.map (evAtVertex _)` by the `ev` β-rules, hence are
equivalences, and equivalences compose formally
(`SSet.Edge.IsEquivalence.of_compStruct` is the same argument at the
level of `toHoHom`). -/
private theorem isEquivalence_ev_map_tensor {A : SSet.{u}} {a₀ a₁ : A _⦋0⦌}
    (α : Edge a₀ a₁) (hα : α.IsEquivalence)
    {F₀ F₁ : ((ihom A).obj A) _⦋0⦌} (Φ : Edge F₀ F₁)
    (hΦ : Φ.IsEquivalence) :
    ((α.tensor Φ).map ((ihom.ev A).app A)).IsEquivalence := by
  obtain ⟨F₀m, rfl⟩ := (ihomVertexEquiv A A).surjective F₀
  have hC := ((Edge.CompStruct.compId α).tensor
    (Edge.CompStruct.idComp Φ)).map ((ihom.ev A).app A)
  have he1 : ((α.tensor (Edge.id ((ihomVertexEquiv A A) F₀m))).map
      ((ihom.ev A).app A)).edge = (α.map F₀m).edge := by
    simp only [Edge.map_edge]
    exact ihom_ev_app_one_ihomVertexEquiv F₀m α
  have he2 : (((Edge.id a₁).tensor Φ).map
      ((ihom.ev A).app A)).edge = (Φ.map (evAtVertex a₁)).edge := by
    simp only [Edge.map_edge]
    exact (evAtVertex_app_one a₁ Φ.edge).symm
  have h1 : IsIso ((α.tensor
      (Edge.id ((ihomVertexEquiv A A) F₀m))).map
      ((ihom.ev A).app A)).toHoHom :=
    (Edge.isEquivalence_iff _).mp ((hα.map F₀m).of_edge_eq he1.symm)
  have h2 : IsIso (((Edge.id a₁).tensor Φ).map
      ((ihom.ev A).app A)).toHoHom :=
    (Edge.isEquivalence_iff _).mp ((hΦ.map (evAtVertex a₁)).of_edge_eq he2.symm)
  rw [Edge.isEquivalence_iff, ← Edge.toHoHom_comp hC]
  infer_instance

/-! ## §4b. From equivalence edges to homotopies on cores -/

/-- (Copy of the private lemma in `Core.lean`: degenerate cutouts are
equivalences.) -/
private theorem isEquivalence_mk'_map_σ_zero_aux {X : SSet.{u}}
    (x : X _⦋0⦌) :
    (Edge.mk' (X.map (SimplexCategory.σ (0 : Fin 1)).op x)).IsEquivalence :=
  (Edge.isEquivalence_id x).of_edge_eq rfl

/-- (Copy of the private lemma in `Core.lean`: constant cutouts are
equivalences.) -/
private theorem isEquivalence_mk'_map_const_aux {X : SSet.{u}}
    {Δ : SimplexCategory} (x : X.obj (op Δ)) (i : Fin (Δ.len + 1)) :
    (Edge.mk' (X.map (SimplexCategory.const ⦋1⦌ Δ i).op x)).IsEquivalence := by
  have hσ : SimplexCategory.σ (0 : Fin 1) =
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 :=
    SimplexCategory.eq_const_to_zero _
  have hφ : SimplexCategory.const ⦋1⦌ Δ i =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ Δ i := by
    rw [hσ]
    exact (SimplexCategory.const_fac_thru_zero ⦋1⦌ Δ i).symm
  rw [hφ, op_comp, X.map_comp]
  exact isEquivalence_mk'_map_σ_zero_aux _

/-- The Yoneda name of a `1`-simplex evaluates by the corresponding
face/degeneracy operator. -/
private theorem yonedaEquiv_symm_app_one {X : SSet.{u}} (s : X _⦋1⦌)
    (φ : ⦋1⦌ ⟶ ⦋1⦌) :
    (yonedaEquiv.symm s).app (op ⦋1⦌) (stdSimplex.objEquiv.symm φ) =
      X.map φ.op s := rfl

/-- The edge of `Fun(A, A)` cut out by `ẽ` at a `1`-simplex of `Δ[1]`
is an equivalence: the simplex is degenerate (an identity edge) or
the nondegenerate edge (which is `e`). -/
private theorem isEquivalence_mk'_yoneda_app {A : SSet.{u}}
    {u v : ((ihom A).obj A) _⦋0⦌} (e : Edge u v) (he : e.IsEquivalence)
    (t' : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (Edge.mk' ((yonedaEquiv.symm e.edge).app (op ⦋1⦌) t')).IsEquivalence := by
  obtain ⟨φ, rfl⟩ := stdSimplex.objEquiv.symm.surjective t'
  rw [yonedaEquiv_symm_app_one]
  rcases SimplexCategory.eq_of_one_to_one φ with ⟨a, rfl⟩ | rfl
  · exact isEquivalence_mk'_map_const_aux _ a
  · have h : ((ihom A).obj A).map (𝟙 ⦋1⦌).op e.edge = e.edge := by simp
    rw [h]
    exact he.of_edge_eq rfl

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `0` is the Yoneda name
of that vertex. (Same proof as the private lemma of
`HomotopyIhom.lean`.) -/
private theorem deltaOne_δ_one_eq_aux :
    stdSimplex.δ (1 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (1 : Fin 2) =
      stdSimplex.δ (1 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `1` is the Yoneda name
of that vertex. (Same proof as the private lemma of
`HomotopyIhom.lean`.) -/
private theorem deltaOne_δ_zero_eq_aux :
    stdSimplex.δ (0 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (0 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The right unitor followed by `ι₀` is whiskering with the vertex-`0`
inclusion. (Same proof as the private lemma of `HomotopyIhom.lean`.) -/
private theorem rightUnitor_hom_comp_ι₀_aux {X : SSet.{u}} :
    (ρ_ X).hom ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (1 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₀_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₀_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_one_eq_aux, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

/-- The right unitor followed by `ι₁` is whiskering with the vertex-`1`
inclusion. (Same proof as the private lemma of `HomotopyIhom.lean`.) -/
private theorem rightUnitor_hom_comp_ι₁_aux {X : SSet.{u}} :
    (ρ_ X).hom ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (0 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₁_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₁_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_zero_eq_aux, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

/-- Curried form of the `ι₀`-boundary: currying `ι₀ ≫ uncurry ẽ`
gives the curried name of `p`. -/
private theorem boundary_zero_aux {A : SSet.{u}} {p q : A ⟶ A}
    (e : Edge (ihomVertexEquiv A A p) (ihomVertexEquiv A A q)) :
    MonoidalClosed.curry' (SSet.ι₀ ≫ uncurry (yonedaEquiv.symm e.edge)) =
      MonoidalClosed.curry' p := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry (uncurry (yonedaEquiv.symm e.edge))) =
      MonoidalClosed.curry' (SSet.ι₀ ≫ uncurry (yonedaEquiv.symm e.edge)) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry (uncurry (yonedaEquiv.symm e.edge))) =
      MonoidalClosed.curry ((ρ_ A).hom ≫
        (SSet.ι₀ ≫ uncurry (yonedaEquiv.symm e.edge)))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₀_aux, Category.assoc]
  rw [MonoidalClosed.curry_uncurry] at key
  have hδ : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      Δ0IsoUnit.hom ≫ MonoidalClosed.curry' p := by
    have h1 : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge =
        yonedaEquiv.symm (ihomVertexEquiv A A p) := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply]
      exact e.src_eq
    rw [h1, yonedaEquiv_symm_ihomVertexEquiv]
  rw [hδ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] at key
  exact key.symm

/-- Curried form of the `ι₁`-boundary: currying `ι₁ ≫ uncurry ẽ`
gives the curried name of `q`. -/
private theorem boundary_one_aux {A : SSet.{u}} {p q : A ⟶ A}
    (e : Edge (ihomVertexEquiv A A p) (ihomVertexEquiv A A q)) :
    MonoidalClosed.curry' (SSet.ι₁ ≫ uncurry (yonedaEquiv.symm e.edge)) =
      MonoidalClosed.curry' q := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry (uncurry (yonedaEquiv.symm e.edge))) =
      MonoidalClosed.curry' (SSet.ι₁ ≫ uncurry (yonedaEquiv.symm e.edge)) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry (uncurry (yonedaEquiv.symm e.edge))) =
      MonoidalClosed.curry ((ρ_ A).hom ≫
        (SSet.ι₁ ≫ uncurry (yonedaEquiv.symm e.edge)))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₁_aux, Category.assoc]
  rw [MonoidalClosed.curry_uncurry] at key
  have hδ : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      Δ0IsoUnit.hom ≫ MonoidalClosed.curry' q := by
    have h1 : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge =
        yonedaEquiv.symm (ihomVertexEquiv A A q) := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply]
      exact e.tgt_eq
    rw [h1, yonedaEquiv_symm_ihomVertexEquiv]
  rw [hδ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] at key
  exact key.symm

/-- The `ι₀`-boundary of the uncurried edge is `p`. -/
private theorem uncurry_edge_ι₀ {A : SSet.{u}} {p q : A ⟶ A}
    (e : Edge (ihomVertexEquiv A A p) (ihomVertexEquiv A A q)) :
    SSet.ι₀ ≫ uncurry (yonedaEquiv.symm e.edge) = p :=
  MonoidalClosed.curry'_injective (boundary_zero_aux e)

/-- The `ι₁`-boundary of the uncurried edge is `q`. -/
private theorem uncurry_edge_ι₁ {A : SSet.{u}} {p q : A ⟶ A}
    (e : Edge (ihomVertexEquiv A A p) (ihomVertexEquiv A A q)) :
    SSet.ι₁ ≫ uncurry (yonedaEquiv.symm e.edge) = q :=
  MonoidalClosed.curry'_injective (boundary_one_aux e)

/-- An equivalence edge of `Fun(A, A)` uncurries to a simplicial
homotopy on cores between the restricted maps. The raw cylinder
lands in the core by the prism (§4a) applied to core edges and the
edges cut out by `ẽ` (§4b); the boundaries are the uncurry β-rules. -/
theorem homotopy_core_of_isEquivalence_edge {A : SSet.{u}} {p q : A ⟶ A}
    (e : Edge (ihomVertexEquiv A A p) (ihomVertexEquiv A A q))
    (he : e.IsEquivalence) :
    Nonempty (Homotopy (core.map p) (core.map q)) := by
  set Hraw : (core A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    ((core A).ι ▷ (Δ[1] : SSet.{u})) ≫
      uncurry (yonedaEquiv.symm e.edge) with hHraw
  have edge_mem : ∀ s : ((core A : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) _⦋1⦌,
      (Edge.mk' (Hraw.app (op ⦋1⦌) s)).IsEquivalence := by
    intro s
    have hκ : (Edge.mk' (((core A).ι).app (op ⦋1⦌) s.1)).IsEquivalence := by
      have hmem : s.1.val ∈ (core A).obj (op ⦋1⦌) := s.1.property
      have hι : ((core A).ι).app (op ⦋1⦌) s.1 = s.1.val := rfl
      rw [hι]
      exact mem_core_obj_one_iff.mp hmem
    have hΦ : (Edge.mk' ((yonedaEquiv.symm e.edge).app (op ⦋1⦌)
        s.2)).IsEquivalence :=
      isEquivalence_mk'_yoneda_app e he s.2
    have hdiag := isEquivalence_ev_map_tensor (Edge.mk' _) hκ
      (Edge.mk' _) hΦ
    exact hdiag.of_edge_eq rfl
  have hle : ⊤ ≤ (core A).preimage Hraw := by
    intro Δ x _
    change Hraw.app Δ x ∈ (core A).obj Δ
    change ∀ φ : ⦋1⦌ ⟶ Δ.unop,
      (Edge.mk' (A.map φ.op (Hraw.app Δ x))).IsEquivalence
    intro φ
    have hnat : A.map φ.op (Hraw.app Δ x) =
        Hraw.app (op ⦋1⦌) (((core A : SSet.{u}) ⊗
          (Δ[1] : SSet.{u})).map φ.op x) := by
      have h := Hraw.naturality φ.op
      simp only [op_unop] at h
      have h2 : ((((core A : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).map φ.op ≫
          Hraw.app (op ⦋1⦌))) x =
          ((Hraw.app Δ ≫ A.map φ.op)) x := by rw [h]
      exact h2.symm
    rw [hnat]
    exact edge_mem _
  set H : (core A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (core A : SSet.{u}) :=
    (Subcomplex.topIso _).inv ≫ Subcomplex.homOfLE hle ≫
      (core A).fromPreimage Hraw with hH
  have hHι : H ≫ (core A).ι = Hraw := by
    simp only [hH, Category.assoc, Subcomplex.fromPreimage_ι,
      Subcomplex.homOfLE_ι_assoc]
    rw [← Category.assoc, Subcomplex.topIso_inv_ι, Category.id_comp]
  have hι₀ : SSet.ι₀ ≫ H = core.map p := by
    apply (cancel_mono (core A).ι).mp
    rw [Category.assoc, hHι, core.map_ι, hHraw, ← Category.assoc,
      SSet.ι₀_comp, Category.assoc, uncurry_edge_ι₀ e]
  have hι₁ : SSet.ι₁ ≫ H = core.map q := by
    apply (cancel_mono (core A).ι).mp
    rw [Category.assoc, hHι, core.map_ι, hHraw, ← Category.assoc,
      SSet.ι₁_comp, Category.assoc, uncurry_edge_ι₁ e]
  exact ⟨Homotopy.mkOfH H hι₀ hι₁⟩

/-- **Equivalence ⇒ hequiv on cores**: an equivalence between
quasicategories induces a weak homotopy equivalence
`SSet.KanComplex.W (SSet.core.map F)` of Kan complexes on cores.
The two triangles are equivalence edges
(`SSet.Edge.exists_toHoHom_eq`); uncurrying them gives the
homotopies for `SSet.KanComplex.W.of_homotopy`. -/
theorem HasHoInverse.kanComplexW_core_map {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {F : A ⟶ B}
    (h : HasHoInverse F) :
    KanComplex.W (core.map F) := by
  obtain ⟨G, ⟨β⟩, ⟨α⟩⟩ := h
  have hFAA : Quasicategory ((ihom A).obj A) := inferInstance
  have hFBB : Quasicategory ((ihom B).obj B) := inferInstance
  obtain ⟨eA, heA⟩ := Edge.exists_toHoHom_eq β.hom
  obtain ⟨eB, heB⟩ := Edge.exists_toHoHom_eq α.hom
  have hAe : eA.IsEquivalence := by
    rw [Edge.isEquivalence_iff, heA]
    infer_instance
  have hBe : eB.IsEquivalence := by
    rw [Edge.isEquivalence_iff, heB]
    infer_instance
  obtain ⟨HX⟩ := homotopy_core_of_isEquivalence_edge eA hAe
  obtain ⟨HY⟩ := homotopy_core_of_isEquivalence_edge eB hBe
  rw [core.map_comp, core.map_id] at HX
  rw [core.map_comp, core.map_id] at HY
  exact KanComplex.W.of_homotopy (core.map F) (core.map G) HX HY

end SSet

end
