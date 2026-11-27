/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGRelativeCYCospanGluing

/-!
# Commutativity of the relative Calabi-Yau bar-counit square

The fixed induction units and functor-induced bar maps imply commutativity
of the bar-counit square.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, Theorems 6.1 and 6.2,
Definition 4.11 and diagrams 6.5--6.7. The ground ring is a field; this
composition theorem has no characteristic-zero restriction.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.CategoryTheory.DGInductionCoherenceModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

universe u

private theorem cycle_comp (k : Type u) [Field k] {C : DGCat k}
    {M N P : RightModule k C} (a : M ⟶ N) (b : N ⟶ P) :
    moduleCycle (a ≫ b) = dgComp k (moduleCycle a) (moduleCycle b) rfl := by
  simp only [moduleCycle, DGFunctor.homEquivDGCycles_comp, dgCompZero_def]

private theorem cycle_pushed (k : Type u) [Field k] {C E : DGCat k}
    {f : C ⟶ E} {R : RestrictionModel f} (L : ExtensionModel f R)
    (M N : DGDerivedModules k C) (a : M.obj ⟶ N.obj) :
    moduleCycle (pushedModuleMap L M N a) = L.functor.dgMap 0 (moduleCycle a) := by
  exact congrArg Subtype.val ((DGFunctor.homEquivDGCycles k _ _).apply_symm_apply _)

private theorem cycle_component (k : Type u) [Field k] {C : DGCat k}
    {M N : RightModule k C} (a : M ⟶ N) (x : Cᵒᵖ) (r : ℤ) :
    (DGFunctor.dgApp k 0 x (moduleCycle a) : Cochain _ _ 0).v r r (by omega) =
      (moduleComponent a x).f r := by
  rw [moduleCycle, DGFunctor.dgApp_homEquivDGCycles_apply]
  simp only [moduleComponent, Cocycle.homOf, Cocycle.mk, DGNatTrans.dgApp_eq_dgClosedHom]

private theorem heq_cochain (k : Type u) [Field k]
    (K L K' L' : Cochains k) (eK : K = K') (eL : L = L')
    (a : Cochain K L 0) (b : Cochain K' L' 0) (h : HEq a b) (r : ℤ) :
    a.v r r (by omega) ≫ (eqToIso eL).hom.f r = (eqToIso eK).hom.f r ≫ b.v r r (by omega) := by
  subst K'
  subst L'
  cases h
  simp

@[reassoc]
private theorem restriction_component (k : Type u) [Field k] {A B : DGCat k}
    {f : A ⟶ B} (T : EnvelopingMap f) (R : RestrictionModel T.functor)
    (M N : RightModule k (enveloping B B)) (a : DGHom k 0 M N)
    (x : A) (y : Aᵒᵖ) (r : ℤ) :
    (DGFunctor.dgApp k 0 (moduleIndex A A x y) (R.functor.dgMap 0 a) :
      Cochain _ _ 0).v r r (by omega) ≫
      (restrictionValueIso T R N x y).hom.f r =
    (restrictionValueIso T R M x y).hom.f r ≫
      (DGFunctor.dgApp k 0 (moduleIndex B B (f.obj x) (op (f.obj y.unop))) a :
        Cochain _ _ 0).v r r (by omega) := by
  have h := R.component_eq M N 0 a (moduleIndex A A x y)
  change HEq _ (DGFunctor.dgApp k 0 (op (T.functor.obj (op x, y.unop))) a) at h
  rw [T.object_eq] at h
  exact heq_cochain k _ _ _ _ _ _ _ _ h r


private theorem tensor_comp_cast (k : Type u) [Field k]
    {X Y Z W W' : Cochains k} (a : X ⟶ Y) (b : Z ⟶ W) (h : W = W') :
    a ⊗ₘ (b ≫ eqToHom h) = (a ⊗ₘ b) ≫ eqToHom (congrArg (fun T => Y ⊗ T) h) := by
  calc
    a ⊗ₘ (b ≫ eqToHom h) = (a ≫ 𝟙 Y) ⊗ₘ (b ≫ eqToHom h) := by rw [Category.comp_id]
    _ = (a ⊗ₘ b) ≫ (𝟙 Y ⊗ₘ eqToHom h) := (tensorHom_comp_tensorHom _ _ _ _).symm
    _ = _ := by rw [id_tensorHom, whiskerLeft_eqToHom]

private theorem map_path_comp (k : Type u) [Field k] {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (a b : A) (xs : List A) :
    mapPathTensor (f.comp (Cochains k) g) a xs b =
      mapPathTensor f a xs b ≫ mapPathTensor g (f.obj a) (xs.map f.obj) (f.obj b) ≫
        eqToHom (congrArg (fun ys => pathTensor C (g.obj (f.obj a)) ys (g.obj (f.obj b)))
          (List.map_map : (xs.map f.obj).map g.obj = xs.map (g.obj ∘ f.obj))) := by
  dsimp only [EnrichedFunctor.comp] at *
  induction xs generalizing a with
  | nil =>
    dsimp only [mapPathTensor, List.map, EnrichedFunctor.comp_map]
    simp only [eqToHom_refl, Category.comp_id]
    change (f.map a b ≫ g.map (f.obj a) (f.obj b)) ⊗ₘ (𝟙 _ ≫ 𝟙 _) = _
    rw [tensorHom_comp_tensorHom]
    rfl
  | cons z zs ih =>
    dsimp only [mapPathTensor, List.map, EnrichedFunctor.comp_map]
    rw [ih]
    simp only [← tensorHom_comp_tensorHom]
    rw [tensor_comp_cast]

private theorem map_path_inclusion_comp (k : Type u) [Field k] {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (a b : A) (n : ℕ) (v : PathVertices A n) :
    mapPathTensor (f.comp (Cochains k) g) a v.val b ≫
      Sigma.ι (fun w : PathVertices C n => pathTensor C (g.obj (f.obj a)) w.val (g.obj (f.obj b)))
        (mappedPath (f.comp (Cochains k) g) v) =
    mapPathTensor f a v.val b ≫ mapPathTensor g (f.obj a) (v.val.map f.obj) (f.obj b) ≫
      Sigma.ι (fun w : PathVertices C n => pathTensor C (g.obj (f.obj a)) w.val (g.obj (f.obj b)))
        (mappedPath g (mappedPath f v)) := by
  have hv : mappedPath g (mappedPath f v) = mappedPath (f.comp (Cochains k) g) v := by
    apply Subtype.ext
    dsimp only [mappedPath, EnrichedFunctor.comp_obj]
    rw [List.map_map]
    rfl
  have hi := Sigma.eqToHom_comp_ι
    (fun w : PathVertices C n => pathTensor C (g.obj (f.obj a)) w.val (g.obj (f.obj b))) hv.symm
  rw [map_path_comp]
  simpa only [Category.assoc] using
    congrArg (fun t => mapPathTensor f a v.val b ≫
      mapPathTensor g (f.obj a) (v.val.map f.obj) (f.obj b) ≫ t) hi

private theorem component_comp_zero (k : Type u) [Field k] {C : DGCat k}
    {M N P : RightModule k C} (a : DGHom k 0 M N) (b : DGHom k 0 N P)
    (x : Cᵒᵖ) (r : ℤ) :
    (DGFunctor.dgApp k 0 x (dgComp k a b rfl) : Cochain _ _ 0).v r r (by omega) =
      (DGFunctor.dgApp k 0 x a : Cochain _ _ 0).v r r (by omega) ≫
        (DGFunctor.dgApp k 0 x b : Cochain _ _ 0).v r r (by omega) := by
  rw [DGFunctor.dgApp_dgComp, dgComp_linearHomComplex]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact Cochain.comp_v _ _ rfl r r r (by omega) (by omega)

private theorem restriction_naturality (k : Type u) [Field k] {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (Tf : EnvelopingMap f) (Tg : EnvelopingMap g)
    (Tfg : EnvelopingMap (f ≫ g)) (Rf : RestrictionModel Tf.functor)
    (Rg : RestrictionModel Tg.functor) (Rfg : RestrictionModel Tfg.functor)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg)
    (M N : RightModule k (enveloping C C)) (a : DGHom k 0 M N) :
    dgComp k (Rfg.functor.dgMap 0 a) (moduleCycle (R.iso N).hom) rfl =
      dgComp k (moduleCycle (R.iso M).hom) (Rf.functor.dgMap 0 (Rg.functor.dgMap 0 a)) rfl := by
  apply DGFunctor.dgHom_ext k
  intro q
  let x : A := q.unop.1.unop
  let y : Aᵒᵖ := op q.unop.2
  change DGFunctor.dgApp k 0 (moduleIndex A A x y)
    (dgComp k (Rfg.functor.dgMap 0 a) (moduleCycle (R.iso N).hom) rfl) =
      DGFunctor.dgApp k 0 (moduleIndex A A x y)
        (dgComp k (moduleCycle (R.iso M).hom) (Rf.functor.dgMap 0 (Rg.functor.dgMap 0 a)) rfl)
  apply Cochain.ext₀
  intro r
  simp only [component_comp_zero, cycle_component]
  apply (cancel_mono ((restrictionValueIso Tf Rf (Rg.functor.obj N) x y).hom.f r)).mp
  apply (cancel_mono ((restrictionValueIso Tg Rg N (f.obj x) (op (f.obj y.unop))).hom.f r)).mp
  simp only [Category.assoc, ← HomologicalComplex.comp_f, R.value_eq]
  rw [HomologicalComplex.comp_f, restriction_component]
  erw [restriction_component_assoc]
  erw [restriction_component]
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, R.value_eq]
  rfl

private theorem comp_assoc_zero (k : Type u) [Field k] {C : DGCat k}
    {M N P Q : RightModule k C} (a : DGHom k 0 M N) (b : DGHom k 0 N P)
    (c : DGHom k 0 P Q) :
    dgComp k (dgComp k a b rfl) c rfl = dgComp k a (dgComp k b c rfl) rfl :=
  dgComp_assoc k a b c rfl rfl rfl

private theorem cycle_id (k : Type u) [Field k] {C : DGCat k} (M : RightModule k C) :
    moduleCycle (𝟙 M) = dgId k M := DGFunctor.homEquivDGCycles_id k

private theorem inverse_square (k : Type u) [Field k] {C : DGCat k}
    {M M' N N' : RightModule k C} (I : M ≅ M') (J : N ≅ N')
    (a : DGHom k 0 M N) (b : DGHom k 0 M' N')
    (h : dgComp k a (moduleCycle J.hom) rfl = dgComp k (moduleCycle I.hom) b rfl) :
    dgComp k (moduleCycle I.inv) a rfl = dgComp k b (moduleCycle J.inv) rfl := by
  have hh := congrArg (fun t =>
    dgComp k (moduleCycle I.inv) (dgComp k t (moduleCycle J.inv) rfl) rfl) h
  simp only [comp_assoc_zero] at hh
  rw [← comp_assoc_zero k (moduleCycle I.inv) (moduleCycle I.hom)] at hh
  simpa only [← cycle_comp, Iso.inv_hom_id, Iso.hom_inv_id, cycle_id,
    dgId_dgComp, dgComp_dgId] using hh

private theorem composition_mate (k : Type u) [Field k] {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (Tf : EnvelopingMap f) (Tg : EnvelopingMap g)
    (Tfg : EnvelopingMap (f ≫ g)) (Rf : RestrictionModel Tf.functor)
    (Rg : RestrictionModel Tg.functor) (Rfg : RestrictionModel Tfg.functor)
    (Lf : ExtensionModel Tf.functor Rf) (Lg : ExtensionModel Tg.functor Rg)
    (Lfg : ExtensionModel Tfg.functor Rfg)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg)
    (K : InductionCompositionModel Lf Lg Lfg R)
    (M : DGDerivedModules k (enveloping A A)) (N : DGDerivedModules k (enveloping B B))
    (P : RightModule k (enveloping C C)) (a : (Lf.functor.obj M).obj ⟶ N.obj)
    (b : (Lg.functor.obj N).obj ⟶ P) :
    ((Lfg.homIso M P).hom.f 0)
      (moduleCycle (K.map M ≫ pushedModuleMap Lg (Lf.functor.obj M) N a ≫ b)) =
    dgComp k (((Lf.homIso M N.obj).hom.f 0) (moduleCycle a))
      (dgComp k (Rf.functor.dgMap 0 (((Lg.homIso N P).hom.f 0) (moduleCycle b)))
        (moduleCycle (R.iso P).inv) rfl) rfl := by
  rw [cycle_comp, Lfg.target_naturality, K.mate_eq, compositionUnit]
  simp only [comp_assoc_zero]
  have hn := inverse_square k
    (R.iso (Lg.functor.obj (Lf.functor.obj M)).obj) (R.iso P)
    (Rfg.functor.dgMap 0 (moduleCycle (pushedModuleMap Lg (Lf.functor.obj M) N a ≫ b)))
    (Rf.functor.dgMap 0 (Rg.functor.dgMap 0
      (moduleCycle (pushedModuleMap Lg (Lf.functor.obj M) N a ≫ b))))
    (restriction_naturality k f g Tf Tg Tfg Rf Rg Rfg R _ _ _)
  rw [hn, ← comp_assoc_zero k (Rf.functor.dgMap 0 (Lg.unit (Lf.functor.obj M))),
    ← Rf.functor.dgMap_dgComp]
  rw [← Lg.hom_formula, cycle_comp, cycle_pushed, Lg.source_naturality]
  rw [Rf.functor.dgMap_dgComp]
  simp only [comp_assoc_zero]
  rw [← comp_assoc_zero k (Lf.unit M) (Rf.functor.dgMap 0 (moduleCycle a)), ← Lf.hom_formula]

private theorem coproduct_degree_ext (k : Type u) [Field k] {I : Type u}
    (V : I → Cochains k) (r : ℤ) {N : ModuleCat k} (a b : (∐ V).X r ⟶ N)
    (h : ∀ i, (Sigma.ι V i).f r ≫ a = (Sigma.ι V i).f r ≫ b) : a = b := by
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) r)
    (colimit.isColimit (Discrete.functor V))).hom_ext
  intro i
  exact h i.as

private theorem diagonal_values_ext (k : Type u) [Field k] (C : DGCat k)
    (x : C) (y : Cᵒᵖ) (r : ℤ) (N : ModuleCat.{u} k)
    (a b : DiagonalValues C x y r →ₗ[k] N)
    (h : ∀ (n : ℕ) (v : PathVertices C n) (z : (pathTensor C y.unop v.val x).X (r + (n : ℤ))),
      a (includeDiagonal C x y r n
        ((Sigma.ι (fun w : PathVertices C n => pathTensor C y.unop w.val x) v).f
        (r + (n : ℤ)) z)) =
      b (includeDiagonal C x y r n
        ((Sigma.ι (fun w : PathVertices C n => pathTensor C y.unop w.val x) v).f
        (r + (n : ℤ)) z))) : a = b := by
  classical
  apply DirectSum.linearMap_ext k
  intro n
  have hn : (ModuleCat.ofHom (a.comp (includeDiagonal C x y r n)) :
      (diagonalBarTerm C n x y).X (r + (n : ℤ)) ⟶ N) =
      ModuleCat.ofHom (b.comp (includeDiagonal C x y r n)) := by
    apply coproduct_degree_ext k
    intro v
    apply ModuleCat.hom_ext
    ext z
    exact h n v z
  exact congrArg ModuleCat.Hom.hom hn

@[reassoc]
private theorem restriction_iso_value (k : Type u) [Field k] {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (Tf : EnvelopingMap f) (Tg : EnvelopingMap g)
    (Tfg : EnvelopingMap (f ≫ g)) (Rf : RestrictionModel Tf.functor)
    (Rg : RestrictionModel Tg.functor) (Rfg : RestrictionModel Tfg.functor)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg)
    (N : RightModule k (enveloping C C)) (x : A) (y : Aᵒᵖ) (r : ℤ) :
    (moduleComponent (R.iso N).hom (moduleIndex A A x y)).f r ≫
      (restrictionValueIso Tf Rf (Rg.functor.obj N) x y).hom.f r ≫
      (restrictionValueIso Tg Rg N (f.obj x) (op (f.obj y.unop))).hom.f r =
      (restrictionValueIso Tfg Rfg N x y).hom.f r := by
  simpa only [HomologicalComplex.comp_f] using congrArg (fun a => a.f r) (R.value_eq N x y)

private theorem bar_restriction_comp (k : Type u) [Field k] {A B C : DGCat k}
    (S : NegativeTraceSystem k) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (DC : CYCategoryData S C) (f : A ⟶ B) (g : B ⟶ C)
    (F : RelativeCYContext S f DA DB) (G : RelativeCYContext S g DB DC)
    (FG : RelativeCYContext S (f ≫ g) DA DC)
    (R : RestrictionCompositionModel f g F.enveloping G.enveloping FG.enveloping
      F.restriction G.restriction FG.restriction) :
    dgComp k (moduleCycle F.barMap.map)
      (F.restriction.functor.dgMap 0 (moduleCycle G.barMap.map)) rfl =
    dgComp k (moduleCycle FG.barMap.map) (moduleCycle (R.iso DC.bar.module).hom) rfl := by
  classical
  apply DGFunctor.dgHom_ext k
  intro q
  let x : A := q.unop.1.unop
  let y : Aᵒᵖ := op q.unop.2
  change DGFunctor.dgApp k 0 (moduleIndex A A x y)
    (dgComp k (moduleCycle F.barMap.map)
      (F.restriction.functor.dgMap 0 (moduleCycle G.barMap.map)) rfl) =
    DGFunctor.dgApp k 0 (moduleIndex A A x y)
      (dgComp k (moduleCycle FG.barMap.map) (moduleCycle (R.iso DC.bar.module).hom) rfl)
  apply Cochain.ext₀
  intro r
  simp only [component_comp_zero, cycle_component]
  apply (cancel_mono
    ((restrictionValueIso F.enveloping F.restriction
      (G.restriction.functor.obj DC.bar.module) x y).hom.f r)).mp
  apply (cancel_mono
    ((restrictionValueIso G.enveloping G.restriction DC.bar.module
      (f.obj x) (op (f.obj y.unop))).hom.f r)).mp
  apply (cancel_mono (DC.bar.termIso (g.obj (f.obj x)) (op (g.obj (f.obj y.unop))) r).hom).mp
  simp only [Category.assoc]
  erw [restriction_component_assoc]
  rw [cycle_component]
  erw [restriction_iso_value_assoc]
  apply (cancel_epi (DA.bar.termIso x y r).inv).mp
  apply ModuleCat.hom_ext
  apply diagonal_values_ext k A x y r
  intro n v z
  simp only [ConcreteCategory.comp_apply]
  have hf := congrArg (DB.bar.termIso (f.obj x) (op (f.obj y.unop)) r).inv
    (F.barMap.normalized x y r n v z)
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hf
  simp only [ConcreteCategory.comp_apply] at hf
  rw [hf]
  rw [G.barMap.normalized]
  erw [FG.barMap.normalized]
  apply congrArg (includeDiagonal C (g.obj (f.obj x)) (op (g.obj (f.obj y.unop))) r n)
  have hp := (congrArg (fun a => a.f (r + (n : ℤ)) z)
    (map_path_inclusion_comp k f g y.unop x n v)).symm
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hp
  convert hp using 1 <;> rfl

private theorem composite_counit (k : Type u) [Field k] {A B C : DGCat k}
    (S : NegativeTraceSystem k) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (DC : CYCategoryData S C) (f : A ⟶ B) (g : B ⟶ C)
    (F : RelativeCYContext S f DA DB) (G : RelativeCYContext S g DB DC)
    (FG : RelativeCYContext S (f ≫ g) DA DC)
    (R : RestrictionCompositionModel f g F.enveloping G.enveloping FG.enveloping
      F.restriction G.restriction FG.restriction)
    (K : InductionCompositionModel F.induction G.induction FG.induction R) :
    K.map ⟨DA.bar.module, DA.bar.cofibrant⟩ ≫
      pushedModuleMap G.induction (pushedDiagonal F.induction DA.bar)
        ⟨DB.bar.module, DB.bar.cofibrant⟩ F.counit.map ≫ G.counit.map = FG.counit.map := by
  apply (DGFunctor.homEquivDGCycles k _ _).injective
  apply Subtype.ext
  apply ((HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) 0).mapIso
    (FG.induction.homIso ⟨DA.bar.module, DA.bar.cofibrant⟩ DC.bar.module)).toLinearEquiv.injective
  change ((FG.induction.homIso ⟨DA.bar.module, DA.bar.cofibrant⟩ DC.bar.module).hom.f 0)
    (moduleCycle _) =
      ((FG.induction.homIso ⟨DA.bar.module, DA.bar.cofibrant⟩ DC.bar.module).hom.f 0)
      (moduleCycle FG.counit.map)
  dsimp only [pushedDiagonal]
  erw [composition_mate]
  rw [F.counit.normalized, G.counit.normalized, FG.counit.normalized]
  rw [← comp_assoc_zero, bar_restriction_comp k S DA DB DC f g F G FG R, comp_assoc_zero]
  rw [← cycle_comp, Iso.hom_inv_id, cycle_id, dgComp_dgId]

private theorem cast_counit (k : Type u) [Field k] {A B : DGCat k}
    (S : NegativeTraceSystem k) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (f g : A ⟶ B) (F : RelativeCYContext S f DA DB) (h : f = g) :
    (eqToIso (congrArg (fun L => (L.obj ⟨DA.bar.module, DA.bar.cofibrant⟩).obj)
      (castContext_induction F h).symm)).hom ≫ (castContext F h).counit.map = F.counit.map := by
  cases h
  simp only [castContext, eqToIso_refl, Iso.refl_hom, Category.id_comp]

namespace WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.CategoryTheory.DGRelativeCYCospanGluing
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels

/-- The bar-counit square commutes by the fixed native induction units and actual bar maps. -/
public theorem relative_cy_bar_counit_square (k : Type u) [Field k] (P : Cospan (k := k))
    (S : NegativeTraceSystem k) (n : ℤ) (D : ModuleData P S n) (K : InductionData D) :
  BarCounitSquare D K
    := by
  refine ⟨?_⟩
  dsimp only [InductionData.topCounit, InductionData.leftCounit]
  simp only [Category.assoc]
  rw [composite_counit k S D.DB D.DX D.DZ P.f P.i D.F D.I D.M K.restrictionFI K.FI,
    composite_counit k S D.DB D.DY D.DZ P.g P.j D.G D.J D.middleGJ K.restrictionGJ K.GJ]
  exact (cast_counit k S D.DB D.DZ P.middle (P.g ≫ P.j) D.M P.square).symm

end WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted
