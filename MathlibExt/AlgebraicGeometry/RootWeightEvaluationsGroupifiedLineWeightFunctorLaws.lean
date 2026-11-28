/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootWeightEvaluations
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Functoriality of groupified root-weight line arrows

This module proves `groupifiedLineWeightFunctorLaws`, the identity and composition laws
for the fixed section-induced maps `RootWeightEvaluations.lineArrow`.

Source: Niels Borne and Angelo Vistoli, *Parabolic sheaves on logarithmic schemes*,
https://arxiv.org/abs/1001.0466v2, Proposition 5.2/Corollary 5.4 and
the root-weight functor used in Theorem 6.1.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open MathlibExt.AlgebraicGeometry.RootWeightEvaluations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public noncomputable section

private instance counit_isIso (X : Scheme.{u}) (M : X.Modules) :
    IsIso ((moduleAdjunction X).counit.app M) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let : IsIso adj.counit := by dsimp [adj]; infer_instance
  exact NatIso.isIso_app_of_isIso adj.counit M

private def insertSection {X : Scheme.{u}} {L : X.Modules}
    (s : Section L) (M : X.Modules) : M ⟶ moduleTensor X L M :=
  (tensorLeftUnit X M).inv ≫ tensorMap s (𝟙 M)

private theorem insertSection_eq {X : Scheme.{u}} {L : X.Modules}
    (s : Section L) (M : X.Modules) :
    insertSection s M = inv ((moduleAdjunction X).counit.app M) ≫
      (sheafifyModules X).map ((λ_ ((forgetModules X).obj M)).inv ≫
        ((forgetModules X).map s ⊗ₘ 𝟙 ((forgetModules X).obj M))) := by
  dsimp only [insertSection, tensorLeftUnit, Iso.trans_inv, Functor.mapIso_inv, asIso_inv]
  rw [tensorMap_eq, CategoryTheory.Functor.map_id, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

private theorem forget_insertSection {X : Scheme.{u}} {L : X.Modules}
    (s : Section L) (M : X.Modules) :
    (forgetModules X).map (insertSection s M) =
      (λ_ ((forgetModules X).obj M)).inv ≫
        ((forgetModules X).map s ⊗ₘ 𝟙 ((forgetModules X).obj M)) ≫
          (moduleAdjunction X).unit.app
            ((forgetModules X).obj L ⊗ (forgetModules X).obj M) := by
  rw [insertSection_eq, CategoryTheory.Functor.map_comp]
  have h : (forgetModules X).map (inv ((moduleAdjunction X).counit.app M)) =
      (moduleAdjunction X).unit.app ((forgetModules X).obj M) := by
    apply (cancel_mono ((forgetModules X).map ((moduleAdjunction X).counit.app M))).1
    rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    exact ((moduleAdjunction X).right_triangle_components M).symm
  rw [h]
  exact (moduleAdjunction X).unit_naturality _

private theorem insertSection_natural {X : Scheme.{u}} {L M N : X.Modules}
    (s : Section L) (f : M ⟶ N) :
    f ≫ insertSection s N = insertSection s M ≫ tensorMap (𝟙 L) f := by
  apply SheafOfModules.hom_ext
  change (forgetModules X).map (f ≫ insertSection s N) =
    (forgetModules X).map (insertSection s M ≫ tensorMap (𝟙 L) f)
  simp only [CategoryTheory.Functor.map_comp, forget_insertSection, tensorMap_eq,
    CategoryTheory.Functor.map_id, Category.assoc]
  rw [(moduleAdjunction X).unit_naturality
    (𝟙 ((forgetModules X).obj L) ⊗ₘ (forgetModules X).map f)]
  rw [← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc, ← id_tensorHom]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]

private theorem insertSection_apply {X : Scheme.{u}} {L : X.Modules}
    (s : Section L) (M : X.Modules) (U : X.Opensᵒᵖ)
    (m : ((forgetModules X).obj M).obj U) :
    ((forgetModules X).map (insertSection s M)).app' U m =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U
          (((forgetModules X).map s).app' U (1 : X.sheaf.obj.obj U) ⊗ₜ m) := by
  rw [forget_insertSection]
  rfl

private theorem tensorMap_apply {X : Scheme.{u}} {L L' M M' : X.Modules}
    (f : L ⟶ L') (g : M ⟶ M') (U : X.Opensᵒᵖ)
    (l : ((forgetModules X).obj L).obj U) (m : ((forgetModules X).obj M).obj U) :
    ((forgetModules X).map (tensorMap f g)).app' U
      (((moduleAdjunction X).unit.app
        ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (l ⊗ₜ m)) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj L' ⊗ (forgetModules X).obj M')).app' U
          (((forgetModules X).map f).app' U l ⊗ₜ ((forgetModules X).map g).app' U m) := by
  rw [tensorMap_eq]
  exact unit_naturality_apply X
    ((forgetModules X).map f ⊗ₘ (forgetModules X).map g) U (l ⊗ₜ m)

private theorem tensorSection_eq {X : Scheme.{u}} {L M : X.Modules}
    (s : Section L) (t : Section M) :
    tensorSection s t = insertSection s (structureModule X) ≫ tensorMap (𝟙 L) t := by
  dsimp only [tensorSection, insertSection]
  rw [Category.assoc, ← tensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  rfl

private theorem tensorSection_apply {X : Scheme.{u}} {L M : X.Modules}
    (s : Section L) (t : Section M) (U : X.Opensᵒᵖ) :
    ((forgetModules X).map (tensorSection s t)).app' U (1 : X.sheaf.obj.obj U) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U
          (((forgetModules X).map s).app' U (1 : X.sheaf.obj.obj U) ⊗ₜ
            ((forgetModules X).map t).app' U (1 : X.sheaf.obj.obj U)) := by
  rw [tensorSection_eq, CategoryTheory.Functor.map_comp]
  change ((forgetModules X).map (tensorMap (𝟙 L) t)).app' U
    (((forgetModules X).map (insertSection s (structureModule X))).app' U
      (1 : X.sheaf.obj.obj U)) = _
  rw [insertSection_apply, tensorMap_apply]
  rfl

private theorem insertSection_assoc {X : Scheme.{u}} {L M : X.Modules}
    (s : Section L) (t : Section M) (N : X.Modules) :
    insertSection t N ≫ insertSection s (moduleTensor X M N) =
      insertSection (tensorSection s t) N ≫ (tensorAssociator X L M N).hom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext n
  change ((forgetModules X).map (insertSection s (moduleTensor X M N))).app' U
    (((forgetModules X).map (insertSection t N)).app' U n) =
      ((forgetModules X).map (tensorAssociator X L M N).hom).app' U
        (((forgetModules X).map (insertSection (tensorSection s t) N)).app' U n)
  rw [insertSection_apply, insertSection_apply, insertSection_apply, tensorSection_apply]
  exact (tensorAssociator_hom_apply_tmul X L M N U
    (((forgetModules X).map s).app' U (1 : X.sheaf.obj.obj U))
    (((forgetModules X).map t).app' U (1 : X.sheaf.obj.obj U)) n).symm

private theorem insertSection_post {X : Scheme.{u}} {L L' : X.Modules}
    (s : Section L) (f : L ⟶ L') (M : X.Modules) :
    insertSection (s ≫ f) M = insertSection s M ≫ tensorMap f (𝟙 M) := by
  dsimp only [insertSection]
  rw [Category.assoc, ← tensorMap_comp]
  simp only [Category.comp_id]

private theorem tensorSection_post {X : Scheme.{u}} {L L' M M' : X.Modules}
    (s : Section L) (t : Section M) (f : L ⟶ L') (g : M ⟶ M') :
    tensorSection (s ≫ f) (t ≫ g) = tensorSection s t ≫ tensorMap f g := by
  simp only [tensorSection, tensorMap_comp, Category.assoc]

private def groupSection {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) (p : P) :
    Section (G.line (Algebra.GrothendieckGroup.of p)) :=
  D.sectionMap p ≫ (G.positive p).inv

private theorem groupSection_unit {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) :
    groupSection G 1 ≫
      eqToHom (congrArg G.line (map_one Algebra.GrothendieckGroup.of)) ≫ G.unit.hom =
        𝟙 (structureModule Y) := by
  dsimp only [groupSection]
  rw [Category.assoc, ← G.positive_unit, Iso.inv_hom_id_assoc]
  exact D.unit_section

private theorem groupSection_mul {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) (p q : P) :
    tensorSection (groupSection G p) (groupSection G q) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of p) (Algebra.GrothendieckGroup.of q)).hom ≫
        eqToHom (congrArg G.line (map_mul Algebra.GrothendieckGroup.of p q).symm) =
          groupSection G (p*q) := by
  apply (cancel_mono (G.positive (p*q)).hom).1
  rw [Category.assoc, Category.assoc, ← G.positive_multiplication]
  simp only [groupSection, tensorSection_post, Category.assoc]
  rw [← Category.assoc (tensorMap (G.positive p).inv (G.positive q).inv)
    (tensorMap (G.positive p).hom (G.positive q).hom) (D.multiplication p q).hom,
    ← tensorMap_comp]
  simp only [Iso.inv_hom_id, tensorMap_id, Category.id_comp]
  exact D.multiplication_section p q

private theorem lineArrow_eq {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D)
    {v w : Weight P} (a : v ⟶ w) :
    lineArrow G a = insertSection (groupSection G a.label) (G.line v.value) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of a.label) v.value).hom ≫
        eqToHom (congrArg G.line a.equation) := by
  rw [groupSection, insertSection_post]
  simp only [lineArrow, insertSection, Category.assoc]

private theorem groupAssociativity {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) (p q r : Groupification P) :
    tensorMap (G.multiplication p q).hom (𝟙 (G.line r)) ≫ (G.multiplication (p*q) r).hom =
      (tensorAssociator Y (G.line p) (G.line q) (G.line r)).hom ≫
        tensorMap (𝟙 (G.line p)) (G.multiplication q r).hom ≫
          (G.multiplication p (q*r)).hom ≫ eqToHom (congrArg G.line (mul_assoc p q r).symm) := by
  apply (cancel_epi (tripleLeft Y (G.line p) (G.line q) (G.line r))).1
  simpa only [← Category.assoc, tripleLeft_comp_tensorAssociator_hom] using G.associativity p q r

private theorem multiplication_transport {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D)
    {p p' q q' : Groupification P} (hp : p = p') (hq : q = q') :
    tensorMap (eqToHom (congrArg G.line hp)) (eqToHom (congrArg G.line hq)) ≫
      (G.multiplication p' q').hom = (G.multiplication p q).hom ≫
        eqToHom (congrArg G.line (congrArg₂ (· * ·) hp hq)) := by
  subst p'
  subst q'
  simp only [eqToHom_refl, tensorMap_id, Category.id_comp, Category.comp_id]

private theorem groupified_identity {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) (v : Weight P) :
    lineArrow G (𝟙 v) = 𝟙 (G.line v.value) := by
  rw [lineArrow_eq]
  change insertSection (groupSection G 1) (G.line v.value) ≫
    (G.multiplication (Algebra.GrothendieckGroup.of 1) v.value).hom ≫
      eqToHom (congrArg G.line (𝟙 v : v ⟶ v).equation) = _
  have h := multiplication_transport G (map_one Algebra.GrothendieckGroup.of)
    (rfl : v.value = v.value)
  simp only [eqToHom_refl] at h
  have hc : eqToHom (congrArg G.line (𝟙 v : v ⟶ v).equation) =
      eqToHom (congrArg G.line (congrArg₂ (· * ·)
        (map_one Algebra.GrothendieckGroup.of) (rfl : v.value = v.value))) ≫
      eqToHom (congrArg G.line (one_mul v.value)) := by
    rw [eqToHom_trans]
  rw [hc, ← Category.assoc (G.multiplication _ _).hom, ← h]
  simp only [Category.assoc]
  rw [G.left_unit]
  slice_lhs 1 3 =>
    rw [← Category.assoc, ← insertSection_post, ← insertSection_post,
      Category.assoc, groupSection_unit]
  simp only [insertSection, tensorMap_id, Category.comp_id, Iso.inv_hom_id]

private theorem groupStep_composition {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) (p q : P)
    (v : Groupification P) :
    insertSection (groupSection G (q*p)) (G.line v) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of (q*p)) v).hom ≫
        eqToHom (congrArg G.line (by rw [map_mul, mul_assoc])) =
    insertSection (groupSection G p) (G.line v) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of p) v).hom ≫
        insertSection (groupSection G q) (G.line (Algebra.GrothendieckGroup.of p * v)) ≫
          (G.multiplication (Algebra.GrothendieckGroup.of q)
            (Algebra.GrothendieckGroup.of p * v)).hom := by
  have hs := groupSection_mul G q p
  rw [← Category.assoc] at hs
  rw [← hs, insertSection_post, insertSection_post]
  have h := multiplication_transport G (map_mul Algebra.GrothendieckGroup.of q p).symm
    (rfl : v = v)
  simp only [eqToHom_refl] at h
  have hc : eqToHom (congrArg G.line (by rw [map_mul, mul_assoc] :
      Algebra.GrothendieckGroup.of (q*p) * v =
        Algebra.GrothendieckGroup.of q * (Algebra.GrothendieckGroup.of p * v))) =
      eqToHom (congrArg G.line (congrArg₂ (· * ·)
        (map_mul Algebra.GrothendieckGroup.of q p) (rfl : v = v))) ≫
      eqToHom (congrArg G.line (mul_assoc (Algebra.GrothendieckGroup.of q)
        (Algebra.GrothendieckGroup.of p) v)) := by
    rw [eqToHom_trans]
  rw [hc]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  slice_lhs 2 3 => rw [groupAssociativity]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  slice_lhs 1 2 => rw [← insertSection_assoc]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← insertSection_natural]
  simp only [Category.assoc]

private theorem groupified_composition {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D)
    {v w z : Weight P} (a : v ⟶ w) (b : w ⟶ z) :
    lineArrow G (a ≫ b) = lineArrow G a ≫ lineArrow G b := by
  rcases v with ⟨v⟩
  rcases w with ⟨w⟩
  rcases z with ⟨z⟩
  rcases a with ⟨p, hp⟩
  rcases b with ⟨q, hq⟩
  dsimp at hp hq
  subst w
  subst z
  let c : (⟨v⟩ : Weight P) ⟶
      ⟨Algebra.GrothendieckGroup.of q * (Algebra.GrothendieckGroup.of p * v)⟩ :=
    ⟨q*p, by dsimp; rw [map_mul, mul_assoc]⟩
  have h : (⟨p, rfl⟩ : (⟨v⟩ : Weight P) ⟶ ⟨Algebra.GrothendieckGroup.of p * v⟩) ≫
      (⟨q, rfl⟩ : (⟨Algebra.GrothendieckGroup.of p * v⟩ : Weight P) ⟶
        ⟨Algebra.GrothendieckGroup.of q * (Algebra.GrothendieckGroup.of p * v)⟩) = c := by
    apply WeightHom.ext
    exact mul_comm p q
  rw [h, lineArrow_eq, lineArrow_eq, lineArrow_eq]
  change insertSection (groupSection G (q*p)) (G.line v) ≫
    (G.multiplication (Algebra.GrothendieckGroup.of (q*p)) v).hom ≫
      eqToHom (congrArg G.line (by rw [map_mul, mul_assoc])) =
    (insertSection (groupSection G p) (G.line v) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of p) v).hom ≫ 𝟙 _) ≫
    insertSection (groupSection G q) (G.line (Algebra.GrothendieckGroup.of p * v)) ≫
      (G.multiplication (Algebra.GrothendieckGroup.of q)
        (Algebra.GrothendieckGroup.of p * v)).hom ≫ 𝟙 _
  simpa only [Category.comp_id, Category.assoc] using groupStep_composition G p q v

/-- **Root-weight line arrows of a groupified chart are functorial.** Let $Y$ be a scheme, $P$ a
commutative monoid, $D$ a Deligne–Faltings chart of $Y$ over $P$ (line bundles $L_p$ with sections
$s_p$ for $p \in P$, compatible with units and tensor products) and $G$ an extension of $D$ to the
groupification $P^{\mathrm{gp}}$ (line bundles $L_v$ for $v \in P^{\mathrm{gp}}$, with unit and
multiplication isomorphisms and identifications $L_{[p]} \cong L_p$). For a weight arrow
$a : v \to w$ labelled by $p \in P$ with $[p]\,v = w$, let $L_v \to L_w$ (`lineArrow G a`) be
tensoring with the section $s_p$, followed by $L_p \cong L_{[p]}$ and the multiplication
$L_{[p]} \otimes L_v \cong L_w$. These arrows send identities to identities and composites to
composites (`LineFunctorLaws G`). -/
theorem groupifiedLineWeightFunctorLaws (Y : Scheme.{u}) (P : CommMonCat.{u})
    (D : DeligneFaltingsChart Y P) (G : GroupifiedChart D) : LineFunctorLaws G
    := by
  exact ⟨groupified_identity G, groupified_composition G⟩
