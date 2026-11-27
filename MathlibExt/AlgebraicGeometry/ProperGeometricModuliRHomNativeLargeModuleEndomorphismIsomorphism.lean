/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
import MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts

/-!
# The native large-module endomorphism map is an isomorphism

The componentwise endomorphism map attached to a native large
projective-module lift is an isomorphism of cochain complexes over the
large scalars. The proof descends each degree along the
coefficient-universe equivalence and checks injectivity and
surjectivity componentwise.

References: Toen--Vaquie math/0503269v5, Sections3.1/3.3/3.5 and the
restricted-Yoneda/derived tensor background cited there. Native
proper-flat-finitely-presented algebraic-space source adaptation is
explicit work, at Stacks03G8/06YY/0DLD/0DLE and AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. No unrestricted equivalence
with absolute perfect complexes on a singular proper source is stated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProperGeometricModuliRHomWanted

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
open CochainComplex.HomComplex

universe u

/-- Upward universe embedding as a semilinear map into the coefficient lift. -/
private def upS (k : Type u) [CommRing k] (V : ModuleCat.{u} k) :
    (V : Type u) →ₛₗ[(↑((ULift.ringEquiv (R := k)).symm) :
      k →+* LargeScalar k)] ((coefficientLift k).obj V : Type (u + 1)) where
  toFun a := (ULift.up a : (coefficientLift k).obj V)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Downward universe projection as a semilinear map out of the coefficient lift. -/
private def downS (k : Type u) [CommRing k] (V : ModuleCat.{u} k) :
    ((coefficientLift k).obj V : Type (u + 1)) →ₛₗ[(↑(ULift.ringEquiv (R := k)) :
      LargeScalar k →+* k)] (V : Type u) where
  toFun x := ((x : (coefficientLift k).obj V) : ULift (V : Type u)).down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Descent of a lifted linear map to the original modules. -/
private def descendLinear (k : Type u) [CommRing k] (V W : ModuleCat.{u} k)
    (g : (coefficientLift k).obj V ⟶ (coefficientLift k).obj W) : V ⟶ W :=
  haveI := RingHomInvPair.of_ringEquiv (ULift.ringEquiv (R := k))
  ModuleCat.ofHom ((downS k W).comp ((g.hom.comp (upS k V))))

/-- A descended map applies by evaluating upstairs on lifted elements and projecting. -/
private theorem descendLinear_apply (k : Type u) [CommRing k]
    (V W : ModuleCat.{u} k)
    (g : (coefficientLift k).obj V ⟶ (coefficientLift k).obj W) (a : (V : Type u)) :
    (descendLinear k V W g).hom a
      = ((g (ULift.up a : (coefficientLift k).obj V) :
        (coefficientLift k).obj W) : ULift (W : Type u)).down := rfl

/-- The coefficient lift of a map applies by mapping downstairs and lifting. -/
private theorem coeffLift_map_apply (k : Type u) [CommRing k]
    (V W : ModuleCat.{u} k) (f : V ⟶ W) (x : (coefficientLift k).obj V) :
    (((coefficientLift k).map f) x : (coefficientLift k).obj W)
      = (ULift.up (f.hom ((x : ULift (V : Type u)).down)) :
        (coefficientLift k).obj W) := rfl

/-- The coefficient lift of a map sends lifted elements to lifted values. -/
private theorem coeffLift_map_apply_up (k : Type u) [CommRing k]
    (V W : ModuleCat.{u} k) (f : V ⟶ W) (a : (V : Type u)) :
    (((coefficientLift k).map f) (ULift.up a : (coefficientLift k).obj V) :
        (coefficientLift k).obj W)
      = (ULift.up (f.hom a) : (coefficientLift k).obj W) := rfl

/-- Lifting after projecting is the identity on the coefficient lift. -/
private theorem up_down' (k : Type u) [CommRing k] (V : ModuleCat.{u} k)
    (x : (coefficientLift k).obj V) :
    (ULift.up ((x : ULift (V : Type u)).down) : (coefficientLift k).obj V) = x :=
  ULift.up_down x

/-- Projecting after lifting is the identity on the original module. -/
private theorem down_up' (k : Type u) [CommRing k] (V : ModuleCat.{u} k)
    (a : (V : Type u)) :
    ((ULift.up a : (coefficientLift k).obj V) : ULift (V : Type u)).down = a := rfl

/-- Lifting the descent of a map recovers the map. -/
private theorem coeffLift_descend (k : Type u) [CommRing k]
    (V W : ModuleCat.{u} k)
    (g : (coefficientLift k).obj V ⟶ (coefficientLift k).obj W) :
    (coefficientLift k).map (descendLinear k V W g) = g := by
  ext x
  rw [coeffLift_map_apply, descendLinear_apply, up_down', up_down']

/-- Descending the lift of a map recovers the map. -/
private theorem descend_coeffLift (k : Type u) [CommRing k]
    (V W : ModuleCat.{u} k) (f : V ⟶ W) :
    descendLinear k V W ((coefficientLift k).map f) = f := by
  ext x
  rw [descendLinear_apply, coeffLift_map_apply_up, down_up']

/-- Components of the homogeneous lift are lifted components. -/
private theorem homogeneousLift_v (k : Type u) [CommRing k]
    (F G : Cochains k) (n i j : ℤ) (a : Cochain F G n) (h : i + n = j) :
    (homogeneousLift k a).v i j h = (coefficientLift k).map (a.v i j h) := rfl

/-- Componentwise descent of a cochain between lifted complexes. -/
private def descendCochain (k : Type u) [CommRing k] (F G : Cochains k) (n : ℤ)
    (γ : Cochain ((largeCochainLift k).obj F) ((largeCochainLift k).obj G) n) :
    Cochain F G n :=
  Cochain.mk (fun p q hpq => descendLinear k (F.X p) (G.X q) (γ.v p q hpq))

/-- Components of the descended cochain are descended components. -/
private theorem descendCochain_v (k : Type u) [CommRing k]
    (F G : Cochains k) (n p q : ℤ)
    (γ : Cochain ((largeCochainLift k).obj F) ((largeCochainLift k).obj G) n)
    (h : p + n = q) :
    (descendCochain k F G n γ).v p q h
      = descendLinear k (F.X p) (G.X q) (γ.v p q h) := rfl

/-- Lifting the descended cochain recovers the cochain. -/
private theorem homogeneousLift_descendCochain (k : Type u) [CommRing k]
    (F G : Cochains k) (n : ℤ)
    (γ : Cochain ((largeCochainLift k).obj F) ((largeCochainLift k).obj G) n) :
    homogeneousLift k (descendCochain k F G n γ) = γ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  change (coefficientLift k).map ((descendCochain k F G n γ).v p q hpq)
    = γ.v p q hpq
  rw [descendCochain_v]
  exact coeffLift_descend k (F.X p) (G.X q) (γ.v p q hpq)

/-- Descending the lifted cochain recovers the cochain. -/
private theorem descendCochain_homogeneousLift (k : Type u) [CommRing k]
    (F G : Cochains k) (n : ℤ) (a : Cochain F G n) :
    descendCochain k F G n (homogeneousLift k a) = a := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  change descendLinear k (F.X p) (G.X q)
      ((homogeneousLift k a).v p q hpq) = a.v p q hpq
  rw [homogeneousLift_v]
  exact descend_coeffLift k (F.X p) (G.X q) (a.v p q hpq)

/-- The homogeneous lift of cochains is injective. -/
private theorem homogeneousLift_injective (k : Type u) [CommRing k]
    (F G : Cochains k) (n : ℤ) :
    Function.Injective (homogeneousLift k :
      Cochain F G n → Cochain ((largeCochainLift k).obj F)
        ((largeCochainLift k).obj G) n) := by
  intro a b h
  have h2 : descendCochain k F G n (homogeneousLift k a)
      = descendCochain k F G n (homogeneousLift k b) := congrArg _ h
  rw [descendCochain_homogeneousLift, descendCochain_homogeneousLift] at h2
  exact h2

/-- The homogeneous lift commutes with unit signs. -/
private theorem homogeneousLift_units_smul (k : Type u) [CommRing k]
    (F G : Cochains k) (n : ℤ) (u : ℤˣ) (z : Cochain F G n) :
    homogeneousLift k (u • z) = u • homogeneousLift k z := by
  obtain rfl | rfl := Int.units_eq_one_or u
  · simp
  · have h1 : ((-(1 : ℤˣ)) • z) = -z := by simp
    have h2 : ((-(1 : ℤˣ)) • homogeneousLift k z) = -homogeneousLift k z := by simp
    rw [h1, h2]
    unfold homogeneousLift
    exact Cochain.map_neg _ _

/-- The homogeneous lift preserves cochain composition. -/
private theorem homogeneousLift_map_comp (k : Type u) [CommRing k]
    (F G K : Cochains k) {p q n : ℤ} (a : Cochain F G p) (b : Cochain G K q)
    (h : p + q = n) :
    homogeneousLift k (Cochain.comp a b h)
      = Cochain.comp (homogeneousLift k a) (homogeneousLift k b) h := by
  unfold homogeneousLift
  exact Cochain.map_comp _ _ _ h _

/-- The homogeneous lift preserves DG composition. -/
private theorem homogeneousLift_dgComp (k : Type u) [CommRing k]
    (F G K : Cochains k) {p q n : ℤ} (a : DGHom k p F G) (b : DGHom k q G K)
    (h : p + q = n) :
    homogeneousLift k (dgComp k a b h)
      = dgComp (LargeScalar k) (X := (largeCochainLift k).obj F)
        (Y := (largeCochainLift k).obj G) (Z := (largeCochainLift k).obj K)
        (homogeneousLift k a) (homogeneousLift k b) h := by
  rw [dgComp_linearHomComplex, dgComp_linearHomComplex, homogeneousLift_units_smul,
    homogeneousLift_map_comp]

/-- Transport of a cochain along object equalities. -/
private def castCochain (k : Type u) [CommRing k]
    {A A' B B' : Cochains (LargeScalar k)} (hA : A = A') (hB : B = B') {n : ℤ}
    (c : Cochain A B n) : Cochain A' B' n := by
  subst hA
  subst hB
  exact c

/-- Transport along reflexivity is the identity. -/
private theorem castCochain_rfl (k : Type u) [CommRing k]
    {A B : Cochains (LargeScalar k)} {n : ℤ} (c : Cochain A B n) :
    castCochain k (rfl : A = A) (rfl : B = B) c = c := rfl

/-- A transported cochain is heterogeneously equal to the original. -/
private theorem heq_castCochain (k : Type u) [CommRing k]
    {A A' B B' : Cochains (LargeScalar k)} (hA : A = A') (hB : B = B') {n : ℤ}
    (c : Cochain A B n) : HEq (castCochain k hA hB c) c := by
  subst hA
  subst hB
  exact HEq.rfl

/-- Transport commutes with DG composition. -/
private theorem castCochain_dgComp (k : Type u) [CommRing k]
    {A A' B B' C C' : Cochains (LargeScalar k)}
    (hA : A = A') (hB : B = B') (hC : C = C')
    {p q n : ℤ} (x : Cochain A B p) (y : Cochain B C q) (h : p + q = n) :
    castCochain k hA hC (dgComp (LargeScalar k) (X := A) (Y := B) (Z := C) x y h)
      = dgComp (LargeScalar k) (X := A') (Y := B') (Z := C')
        (castCochain k hA hB x) (castCochain k hB hC y) h := by
  subst hA
  subst hB
  subst hC
  rfl

/-- Transport commutes with unit signs. -/
private theorem castCochain_units_smul (k : Type u) [CommRing k]
    {A A' B B' : Cochains (LargeScalar k)} (hA : A = A') (hB : B = B')
    {n : ℤ} (u : ℤˣ) (x : Cochain A B n) :
    castCochain k hA hB (u • x) = u • castCochain k hA hB x := by
  subst hA
  subst hB
  rfl

/-- Each degree of the endomorphism map is injective. -/
private theorem endo_injective (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    (n : ℤ) :
    Function.Injective ⇑(ConcreteCategory.hom (ML.endomorphismMap.f n)) := by
  intro x y hxy
  have hxy' : ((ML.endomorphismMap.f n).hom) x
      = ((ML.endomorphismMap.f n).hom) y := hxy
  have hx : x = ULift.up ((x : ULift ((dgHomComplex k M M).X n)).down) :=
    (ULift.up_down _).symm
  have hy : y = ULift.up ((y : ULift ((dgHomComplex k M M).X n)).down) :=
    (ULift.up_down _).symm
  rw [hx, hy] at hxy' ⊢
  suffices h : ((x : ULift ((dgHomComplex k M M).X n)).down)
      = ((y : ULift ((dgHomComplex k M M).X n)).down) by rw [h]
  refine DGFunctor.dgHom_ext (R := k) fun w => ?_
  have e : DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
        (op (ULift.up w.unop))
        ((ML.endomorphismMap.f n).hom
          (ULift.up ((x : ULift ((dgHomComplex k M M).X n)).down)))
      = DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
        (op (ULift.up w.unop))
        ((ML.endomorphismMap.f n).hom
          (ULift.up ((y : ULift ((dgHomComplex k M M).X n)).down))) := by
    rw [hxy']
  have ha := ML.endomorphism_normalized n
    ((x : ULift ((dgHomComplex k M M).X n)).down) w
  have hb := ML.endomorphism_normalized n
    ((y : ULift ((dgHomComplex k M M).X n)).down) w
  have hHEq : HEq
      (homogeneousLift k
        (DGFunctor.dgApp k n w ((x : ULift ((dgHomComplex k M M).X n)).down)))
      (homogeneousLift k
        (DGFunctor.dgApp k n w ((y : ULift ((dgHomComplex k M M).X n)).down))) :=
    HEq.trans (HEq.symm ha) (HEq.trans (heq_of_eq e) hb)
  have hEq := eq_of_heq hHEq
  exact homogeneousLift_injective k _ _ n hEq

/-- Descent of one target component along the value equality. -/
private def descendAt (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    (x : Tᵒᵖ) {n : ℤ}
    (c : Cochain (ML.module.obj.toEnrichedFunctor.obj (op (ULift.up x.unop)))
      (ML.module.obj.toEnrichedFunctor.obj (op (ULift.up x.unop))) n) :
    Cochain (M.toEnrichedFunctor.obj x) (M.toEnrichedFunctor.obj x) n :=
  descendCochain k _ _ n (castCochain k (ML.value_eq x) (ML.value_eq x) c)

/-- Lifting a descended component recovers the transported component. -/
private theorem homogeneousLift_descendAt (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (ML : LargeProjectiveModuleLift UL T M) (x : Tᵒᵖ) {n : ℤ}
    (c : Cochain (ML.module.obj.toEnrichedFunctor.obj (op (ULift.up x.unop)))
      (ML.module.obj.toEnrichedFunctor.obj (op (ULift.up x.unop))) n) :
    homogeneousLift k (descendAt k UL T M ML x c)
      = castCochain k (ML.value_eq x) (ML.value_eq x) c :=
  homogeneousLift_descendCochain k _ _ n _

/-- The transported lifted action is the lifted original action. -/
private theorem cast_action_eq (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    (x y : Tᵒᵖ) {p : ℤ} (f : DGHom k p x y) :
    castCochain k (ML.value_eq x) (ML.value_eq y)
        (ML.module.obj.toEnrichedFunctor.dgMap p
          (X := op (ULift.up x.unop)) (Y := op (ULift.up y.unop)) (ULift.up f))
      = homogeneousLift k (M.toEnrichedFunctor.dgMap p (X := x) (Y := y) f) := by
  apply eq_of_heq
  refine HEq.trans (heq_castCochain k _ _ _) ?_
  exact ML.action_eq x y p f

/-- The family of descended components of a target morphism. -/
private def descendFamily (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    {n : ℤ} (t : DGHom (LargeScalar k) n ML.module.obj ML.module.obj) (x : Tᵒᵖ) :
    DGHom k n (M.toEnrichedFunctor.obj x) (M.toEnrichedFunctor.obj x) :=
  descendAt k UL T M ML x
    (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
      (op (ULift.up x.unop)) t)

/-- Lifting the descended family recovers transported components. -/
private theorem homogeneousLift_descendFamily (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (ML : LargeProjectiveModuleLift UL T M) {n : ℤ}
    (t : DGHom (LargeScalar k) n ML.module.obj ML.module.obj) (x : Tᵒᵖ) :
    homogeneousLift k (descendFamily k UL T M ML t x)
      = castCochain k (ML.value_eq x) (ML.value_eq x)
        (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
          (op (ULift.up x.unop)) t) :=
  homogeneousLift_descendAt k UL T M ML x _

/-- The descended family is natural. -/
private theorem isNatural_descendFamily (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (ML : LargeProjectiveModuleLift UL T M) {n : ℤ}
    (t : DGHom (LargeScalar k) n ML.module.obj ML.module.obj) :
    DGFunctor.IsNatural (F := M) (G := M) (R := k) (n := n)
      (descendFamily k UL T M ML t) := by
  rw [DGFunctor.isNatural_def]
  intro X Y p m f h₁ h₂
  have hnat := DGFunctor.IsNatural.dgComp_dgMap
    (DGFunctor.isNatural_dgApp (R := LargeScalar k) t)
    (X := op (ULift.up X.unop)) (Y := op (ULift.up Y.unop)) (p := p) (m := m)
    (ULift.up f) h₁ h₂
  apply homogeneousLift_injective k _ _ m
  rw [homogeneousLift_dgComp, homogeneousLift_units_smul, homogeneousLift_dgComp,
    ← cast_action_eq k UL T M ML, homogeneousLift_descendFamily,
    homogeneousLift_descendFamily, ← castCochain_dgComp, ← castCochain_dgComp,
    ← castCochain_units_smul]
  exact congrArg (castCochain k (ML.value_eq X) (ML.value_eq Y)) hnat

/-- The descended target morphism as an original DG morphism. -/
private def descendModuleHom (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    {n : ℤ} (t : DGHom (LargeScalar k) n ML.module.obj ML.module.obj) :
    DGHom k n M M :=
  (DGFunctor.dgHomEquiv k M M n).symm
    ⟨descendFamily k UL T M ML t,
      DGFunctor.mem_natTransSubmodule.mpr
        (isNatural_descendFamily k UL T M ML t)⟩

/-- Components of the descended morphism are the descended family. -/
private theorem dgApp_descendModuleHom (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (ML : LargeProjectiveModuleLift UL T M) {n : ℤ}
    (t : DGHom (LargeScalar k) n ML.module.obj ML.module.obj) (x : Tᵒᵖ) :
    DGFunctor.dgApp k n x (descendModuleHom k UL T M ML t)
      = descendFamily k UL T M ML t x :=
  DGFunctor.dgApp_dgHomEquiv_symm_apply k _ x

/-- Every lifted opposite object is a lifted original object. -/
private theorem exists_up_unop (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (z : (↥(liftedDGCategory UL T))ᵒᵖ) :
    ∃ w : ↥T, z = op ((ULift.up w : ULift ↥T) : ↥(liftedDGCategory UL T)) := by
  refine ⟨((z.unop : ULift ↥T).down), ?_⟩
  have h : ((ULift.up (((z.unop : ULift ↥T).down)) : ULift ↥T) :
      ↥(liftedDGCategory UL T)) = z.unop := ULift.up_down _
  exact (op_unop z).symm.trans (congrArg op h.symm)

/-- Each degree of the endomorphism map is surjective. -/
private theorem endo_surjective (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    (n : ℤ) :
    Function.Surjective ⇑(ConcreteCategory.hom (ML.endomorphismMap.f n)) := by
  intro t
  refine ⟨ULift.up (descendModuleHom k UL T M ML t), ?_⟩
  change ((ML.endomorphismMap.f n).hom)
      (ULift.up (descendModuleHom k UL T M ML t)) = t
  refine DGFunctor.dgHom_ext (R := LargeScalar k) fun z => ?_
  obtain ⟨w, rfl⟩ := exists_up_unop k UL T z
  apply eq_of_heq
  have h1 : HEq
      (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
        (op ((ULift.up w : ULift ↥T) : ↥(liftedDGCategory UL T)))
        ((ML.endomorphismMap.f n).hom
          (ULift.up (descendModuleHom k UL T M ML t))))
      (homogeneousLift k
        (DGFunctor.dgApp k n (op w) (descendModuleHom k UL T M ML t))) :=
    ML.endomorphism_normalized n (descendModuleHom k UL T M ML t) (op w)
  have h2 : DGFunctor.dgApp k n (op w) (descendModuleHom k UL T M ML t)
      = descendFamily k UL T M ML t (op w) :=
    dgApp_descendModuleHom k UL T M ML t (op w)
  have h4 : homogeneousLift k (descendFamily k UL T M ML t (op w))
      = castCochain k (ML.value_eq (op w)) (ML.value_eq (op w))
        (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
          (op (ULift.up (op w).unop)) t) :=
    homogeneousLift_descendFamily k UL T M ML t (op w)
  have hmid : HEq
      (homogeneousLift k
        (DGFunctor.dgApp k n (op w) (descendModuleHom k UL T M ML t)))
      (castCochain k (ML.value_eq (op w)) (ML.value_eq (op w))
        (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
          (op (ULift.up (op w).unop)) t)) :=
    heq_of_eq ((congrArg (homogeneousLift k) h2).trans h4)
  have hlast : HEq
      (castCochain k (ML.value_eq (op w)) (ML.value_eq (op w))
        (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
          (op (ULift.up (op w).unop)) t))
      (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory UL T)ᵒᵖ) n
        (op (ULift.up (op w).unop)) t) :=
    heq_castCochain k _ _ _
  exact HEq.trans h1 (HEq.trans hmid hlast)

/-- Each degree of the endomorphism map is an isomorphism. -/
private theorem endo_isIso_degree (k : Type u) [CommRing k] (UL : CochainLiftModel k)
    (T : DGCat k) (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M)
    (n : ℤ) : IsIso (ML.endomorphismMap.f n) := by
  have : Mono (ML.endomorphismMap.f n) :=
    ConcreteCategory.mono_of_injective _ (endo_injective k UL T M ML n)
  have : Epi (ML.endomorphismMap.f n) :=
    ConcreteCategory.epi_of_surjective _ (endo_surjective k UL T M ML n)
  exact isIso_of_mono_of_epi _

/-- Its actual componentwise endomorphism map is a coefficient-universe isomorphism,
not a geometric conclusion. -/
theorem native_large_module_endomorphism_isomorphism (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (ML : LargeProjectiveModuleLift UL T M) : IsIso ML.endomorphismMap := by
  have : ∀ n, IsIso (ML.endomorphismMap.f n) :=
    fun n => endo_isIso_degree k UL T M ML n
  exact HomologicalComplex.Hom.isIso_of_components ML.endomorphismMap

end WantedExt.AlgebraicGeometry.ProperGeometricModuliRHomWanted
