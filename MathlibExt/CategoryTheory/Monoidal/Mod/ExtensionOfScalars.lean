/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# Balanced extension of scalars for internal left modules

For an actual monoid map `p : A ⟶ B`, extension of scalars is the
coequalizer of the right `A` action on `B` and the left action on the input
module. Both functions of the induction/restriction Hom correspondence
are constructed from this parallel pair.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.ExtensionOfScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A B : C} [MonObj A] [MonObj B]
variable (p : A ⟶ B) [IsMonHom p]

/-- The actual right scalar action determined by the monoid map. -/
def rightAction : B ⊗ A ⟶ B := (B ◁ p) ≫ μ[B]

/-- The original right scalar action satisfies the monoid unit equation. -/
@[reassoc]
theorem rightAction_one : (B ◁ η[A]) ≫ rightAction p = (ρ_ B).hom := by
  unfold rightAction
  rw [← Category.assoc, ← whiskerLeft_comp, IsMonHom.one_hom, MonObj.mul_one]

/-- The original right scalar action satisfies the inverse-associator equation. -/
@[reassoc]
theorem rightAction_assoc : (B ◁ μ[A]) ≫ rightAction p =
    (α_ B A A).inv ≫ (rightAction p ▷ A) ≫ rightAction p := by
  have hn : (B ◁ (p ⊗ₘ p)) ≫ (α_ B B B).inv =
      (α_ B A A).inv ≫ ((B ◁ p) ⊗ₘ p) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 B) p p
  calc
    _ = (B ◁ (p ⊗ₘ p)) ≫ (B ◁ μ[B]) ≫ μ[B] := by
      unfold rightAction
      rw [← Category.assoc, ← whiskerLeft_comp, IsMonHom.mul_hom, whiskerLeft_comp]
      simp only [Category.assoc]
    _ = (B ◁ (p ⊗ₘ p)) ≫ (α_ B B B).inv ≫ (μ[B] ▷ B) ≫ μ[B] := by
      rw [MonObj.mul_assoc_flip]
    _ = (α_ B A A).inv ≫ ((B ◁ p) ⊗ₘ p) ≫ (μ[B] ▷ B) ≫ μ[B] := by
      rw [← Category.assoc, ← Category.assoc, hn]
      simp only [Category.assoc]
    _ = (α_ B A A).inv ≫ (rightAction p ▷ A) ≫ rightAction p := by
      simp only [rightAction, comp_whiskerRight, Category.assoc]
      rw [tensorHom_def, Category.assoc, whisker_exchange_assoc]

omit [IsMonHom p] [MonObj A] in
/-- The left sphere action commutes with the right scalar action through the original associator. -/
@[reassoc]
theorem rightAction_middle : (μ[B] ▷ A) ≫ rightAction p =
    (α_ B B A).hom ≫ (B ◁ rightAction p) ≫ μ[B] := by
  unfold rightAction
  rw [← whisker_exchange_assoc, MonObj.mul_assoc]
  rw [associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The original target monoid as a left target/right source bimodule. -/
def scalarBimodule : Bimod ({ X := B } : Mon C) ({ X := A } : Mon C) where
  X := B
  actLeft := μ[B]
  one_actLeft := MonObj.one_mul B
  left_assoc := MonObj.mul_assoc B
  actRight := rightAction p
  actRight_one := rightAction_one p
  right_assoc := rightAction_assoc p
  middle_assoc := rightAction_middle p

/-- Restriction keeps the full input module and precomposes its action with `p`. -/
def restriction : Mod C B ⥤ Mod C A := Mod.comap p

section Colimits

variable [HasColimitsOfSize.{0, 0} C]
variable [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]

/-- Target-monoid preservation supplies all small target-module colimits. -/
theorem moduleColimits : HasColimitsOfSize.{0, 0} (Mod C B) :=
  Mod.hasColimits B

/-- The stronger preservation premise supplies the target coequalizers used by induction. -/
instance targetCoequalizers : HasCoequalizers (Mod C B) := by
  let _ : HasColimitsOfSize.{0, 0} (Mod C B) := moduleColimits (B := B)
  infer_instance

end Colimits

section Coequalizers

variable [HasCoequalizers (Mod C B)]

/-- The generator of a free module uses the original monoid unit. -/
def freeUnit (X : C) : X ⟶ ((Mod.free B).obj X).X :=
  (Mod.freeForgetAdjunction B).unit.app X

/-- The first balancing map is induced by the entire input module action. -/
def leftMap (M : Mod C A) :
    (Mod.free B).obj (A ⊗ M.X) ⟶ (Mod.free B).obj M.X :=
  (Mod.free B).map M.mod.smul

/-- The second balancing map is induced by the original monoid homomorphism. -/
def rightMap (M : Mod C A) :
    (Mod.free B).obj (A ⊗ M.X) ⟶ (Mod.free B).obj M.X :=
  ((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X)
    ((Mod.free B).obj M.X)).symm (p ▷ M.X)

omit [HasCoequalizers (Mod C B)] in
omit [IsMonHom p] in
/-- The first original balancing map retains the entire input action on the literal free carrier. -/
theorem leftMap_hom (M : Mod C A) : (leftMap (B := B) M).hom = B ◁ M.mod.smul := by
  rfl

omit [HasCoequalizers (Mod C B)] in
omit [IsMonHom p] in
/-- The second original balancing map is precisely the right scalar action through the inverse associator. -/
theorem rightMap_hom (M : Mod C A) : (rightMap p M).hom =
    (α_ B A M.X).inv ≫ (rightAction p ▷ M.X) := by
  have h := Mod.freeForgetAdjunction_homEquiv_symm_apply_hom B
    ((Mod.free B).obj M.X) (p ▷ M.X)
  change (rightMap p M).hom = (𝟙 (B ⊗ (A ⊗ M.X))) ≫
    (B ◁ (p ▷ M.X)) ≫ (α_ B B M.X).inv ≫ (μ[B] ▷ M.X) at h
  rw [Category.id_comp] at h
  have hn : (B ◁ (p ▷ M.X)) ≫ (α_ B B M.X).inv =
      (α_ B A M.X).inv ≫ ((B ◁ p) ▷ M.X) :=
    associator_inv_naturality_middle B p M.X
  have he : (B ◁ (p ▷ M.X)) ≫ (α_ B B M.X).inv ≫ (μ[B] ▷ M.X) =
      (α_ B A M.X).inv ≫ (rightAction p ▷ M.X) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f : B ⊗ (A ⊗ M.X) ⟶ (B ⊗ B) ⊗ M.X =>
        f ≫ (μ[B] ▷ M.X)) hn).trans
          (by simp only [rightAction, comp_whiskerRight, Category.assoc]))
  exact h.trans he

/-- The actual balanced left `B` module. -/
def object (M : Mod C A) : Mod C B := coequalizer (rightMap p M) (leftMap (B := B) M)

/-- The balancing quotient is the complete free-module coequalizer map. -/
def π (M : Mod C A) : (Mod.free B).obj M.X ⟶ object p M :=
  coequalizer.π (rightMap p M) (leftMap M)

omit [IsMonHom p] in
@[reassoc]
theorem balance (M : Mod C A) : leftMap M ≫ π p M = rightMap p M ≫ π p M :=
  (coequalizer.condition _ _).symm

/-- The free generator survives as the unit generator of induction. -/
def generator (M : Mod C A) : M.X ⟶ (object p M).X :=
  freeUnit M.X ≫ (π p M).hom

omit [HasCoequalizers (Mod C B)] in
theorem freeHom_apply {X : C} (N : Mod C B) (h : (Mod.free B).obj X ⟶ N) :
    (Mod.freeForgetAdjunction B).homEquiv X N h = freeUnit X ≫ h.hom := by
  exact (Mod.freeForgetAdjunction B).homEquiv_unit X N h

omit [HasCoequalizers (Mod C B)] in
theorem freeHom_symm {X : C} (N : Mod C B) (f : X ⟶ N.X) :
    (((Mod.freeForgetAdjunction B).homEquiv X N).symm f).hom =
      (B ◁ f) ≫ N.mod.smul := by
  have h := Mod.freeForgetAdjunction_homEquiv_symm_apply_hom B N f
  change (((Mod.freeForgetAdjunction B).homEquiv X N).symm f).hom =
    (𝟙 (B ⊗ X)) ≫ (B ◁ f) ≫ N.mod.smul at h
  simpa only [Category.id_comp] using h

omit [HasCoequalizers (Mod C B)] in
omit [IsMonHom p] in
theorem rightMap_Hom {M : Mod C A} (N : Mod C B)
    (h : (Mod.free B).obj M.X ⟶ N) :
    (Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N (rightMap p M ≫ h) =
      (p ▷ M.X) ≫ h.hom := by
  rw [(Mod.freeForgetAdjunction B).homEquiv_naturality_right]
  change ((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) ((Mod.free B).obj M.X))
    (((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) ((Mod.free B).obj M.X)).symm
      (p ▷ M.X)) ≫ h.hom = _
  exact congrArg (fun f : A ⊗ M.X ⟶ ((Mod.free B).obj M.X).X => f ≫ h.hom)
    (((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) ((Mod.free B).obj M.X)).apply_symm_apply
      (p ▷ M.X))

omit [HasCoequalizers (Mod C B)] in
theorem leftMap_Hom {M : Mod C A} (N : Mod C B)
    (h : (Mod.free B).obj M.X ⟶ N) :
    (Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N (leftMap M ≫ h) =
      M.mod.smul ≫ (Mod.freeForgetAdjunction B).homEquiv M.X N h :=
  (Mod.freeForgetAdjunction B).homEquiv_naturality_left _ _

omit [MonObj A] [MonObj B] [IsMonHom p] [HasCoequalizers (Mod C B)] in
theorem scalar_exchange {X Y : C} (f : X ⟶ Y) :
    (p ▷ X) ≫ (B ◁ f) = (A ◁ f) ≫ (p ▷ Y) := by
  exact (whisker_exchange p f).symm

/-- The forward Hom function first reads the original free generator. -/
def toRestriction {M : Mod C A} {N : Mod C B} (h : object p M ⟶ N) :
    M ⟶ (restriction p).obj N := by
  let k : (Mod.free B).obj M.X ⟶ N := π p M ≫ h
  let f : M.X ⟶ N.X := (Mod.freeForgetAdjunction B).homEquiv M.X N k
  refine Mod.Hom.mk' f ?_
  change M.mod.smul ≫ f = (A ◁ f) ≫ (p ▷ N.X) ≫ N.mod.smul
  have hb : leftMap M ≫ k = rightMap p M ≫ k := by
    dsimp only [k]
    rw [← Category.assoc, balance, Category.assoc]
  have he := congrArg ((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N) hb
  rw [leftMap_Hom, rightMap_Hom] at he
  have hk : k.hom = (B ◁ f) ≫ N.mod.smul := by
    simpa only [f, Equiv.symm_apply_apply] using freeHom_symm N f
  rw [hk, ← Category.assoc, scalar_exchange, Category.assoc] at he
  exact he

/-- The inverse Hom function descends the original free adjunct through both balancing maps. -/
def fromRestriction {M : Mod C A} {N : Mod C B} (f : M ⟶ (restriction p).obj N) :
    object p M ⟶ N := by
  let f₀ : M.X ⟶ N.X := f.hom
  let e : ((Mod.free B).obj M.X ⟶ N) ≃ (M.X ⟶ N.X) :=
    (Mod.freeForgetAdjunction B).homEquiv M.X N
  let k : (Mod.free B).obj M.X ⟶ N := e.symm f₀
  have hf : M.mod.smul ≫ f₀ = (A ◁ f₀) ≫ (p ▷ N.X) ≫ N.mod.smul :=
    f.isModHom.smul_hom
  refine coequalizer.desc k ?_
  apply ((Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N).injective
  have hl : (Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N (leftMap M ≫ k) =
      M.mod.smul ≫ f₀ := (leftMap_Hom N k).trans
    (congrArg (fun g : M.X ⟶ N.X => M.mod.smul ≫ g) (e.apply_symm_apply f₀))
  have hk : k.hom = (B ◁ f₀) ≫ N.mod.smul := freeHom_symm N f₀
  have ht : (p ▷ M.X) ≫ k.hom = (A ◁ f₀) ≫ (p ▷ N.X) ≫ N.mod.smul :=
    (congrArg (fun g : B ⊗ M.X ⟶ N.X => (p ▷ M.X) ≫ g) hk).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g : A ⊗ M.X ⟶ B ⊗ N.X => g ≫ N.mod.smul)
          (scalar_exchange p f₀)).trans (Category.assoc _ _ _)))
  have hr : (Mod.freeForgetAdjunction B).homEquiv (A ⊗ M.X) N (rightMap p M ≫ k) =
      (A ◁ f₀) ≫ (p ▷ N.X) ≫ N.mod.smul := (rightMap_Hom p N k).trans ht
  exact hr.trans (hf.symm.trans hl.symm)

@[reassoc]
theorem π_fromRestriction {M : Mod C A} {N : Mod C B}
    (f : M ⟶ (restriction p).obj N) :
    π p M ≫ fromRestriction p f =
      ((Mod.freeForgetAdjunction B).homEquiv M.X N).symm f.hom :=
  by
    unfold π fromRestriction
    exact coequalizer.π_desc (f := rightMap p M) (g := leftMap (B := B) M) _ _

/-- Both original Hom functions are mutually inverse on every whole module morphism. -/
def homEquiv (M : Mod C A) (N : Mod C B) :
    (object p M ⟶ N) ≃ (M ⟶ (restriction p).obj N) where
  toFun := toRestriction p
  invFun := fromRestriction p
  left_inv h := by
    apply coequalizer.hom_ext
    change π p M ≫ fromRestriction p (toRestriction p h) = π p M ≫ h
    calc
      _ = ((Mod.freeForgetAdjunction B).homEquiv M.X N).symm (toRestriction p h).hom :=
        π_fromRestriction p (toRestriction p h)
      _ = π p M ≫ h := ((Mod.freeForgetAdjunction B).homEquiv M.X N).symm_apply_apply _
  right_inv f := by
    apply Mod.hom_ext
    change (Mod.freeForgetAdjunction B).homEquiv M.X N
      (π p M ≫ fromRestriction p f) = f.hom
    exact (congrArg ((Mod.freeForgetAdjunction B).homEquiv M.X N)
      (π_fromRestriction p f)).trans
        (((Mod.freeForgetAdjunction B).homEquiv M.X N).apply_symm_apply f.hom)

/-- The forward original Hom function keeps the literal generator component. -/
theorem toRestriction_hom {M : Mod C A} {N : Mod C B} (h : object p M ⟶ N) :
    (toRestriction p h).hom = generator p M ≫ h.hom := by
  change (Mod.freeForgetAdjunction B).homEquiv M.X N (π p M ≫ h) = _
  rw [freeHom_apply]
  exact (Category.assoc _ _ _).symm

/-- Naturality in every target module map uses the same full component map. -/
theorem homEquiv_naturality_right (M : Mod C A) (N N' : Mod C B)
    (g : N ⟶ N') (h : object p M ⟶ N) :
    homEquiv p M N' (h ≫ g) = homEquiv p M N h ≫ (restriction p).map g := by
  apply Mod.hom_ext
  change (toRestriction p (h ≫ g)).hom = (toRestriction p h).hom ≫ g.hom
  rw [toRestriction_hom, toRestriction_hom]
  exact (Category.assoc _ _ _).symm

/-- The functor maps are derived from the constructed balanced Hom correspondence. -/
def induction : Mod C A ⥤ Mod C B :=
  Adjunction.leftAdjointOfEquiv (homEquiv p) (homEquiv_naturality_right p)

/-- The actual balanced tensor and scalar restriction form the full original adjunction. -/
def adjunction : induction p ⊣ restriction p :=
  Adjunction.adjunctionOfEquivLeft (homEquiv p) (homEquiv_naturality_right p)

/-- The whole chosen adjunction has exactly the two constructed original Hom functions. -/
theorem adjunction_homEquiv (M : Mod C A) (N : Mod C B) :
    (adjunction p).homEquiv M N = homEquiv p M N := by
  unfold adjunction Adjunction.adjunctionOfEquivLeft
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M) N

/-- Every full unit is the original generator read by the forward Hom function. -/
theorem unit_original (M : Mod C A) :
    (adjunction p).unit.app M = toRestriction p (𝟙 (object p M)) := by
  exact ((adjunction p).homEquiv_id M).symm.trans
    (congrArg (fun e => e (𝟙 (object p M))) (adjunction_homEquiv p M (object p M)))

/-- Every full counit is the actual balanced descent of the identity restriction map. -/
theorem counit_original (N : Mod C B) :
    (adjunction p).counit.app N = fromRestriction p (𝟙 ((restriction p).obj N)) := by
  exact ((adjunction p).homEquiv_symm_id N).symm.trans
    (congrArg (fun e => e.symm (𝟙 ((restriction p).obj N)))
      (adjunction_homEquiv p ((restriction p).obj N) N))

/-- The unit keeps the literal original monoid generator on the whole input carrier. -/
theorem unit_hom (M : Mod C A) : ((adjunction p).unit.app M).hom = generator p M := by
  have h := congrArg Mod.Hom.hom (unit_original p M)
  exact h.trans ((toRestriction_hom p (𝟙 (object p M))).trans (Category.comp_id _))

/-- The full counit preserves the original free-forgetful counit at its balancing quotient. -/
@[reassoc]
theorem π_counit (N : Mod C B) :
    π p ((restriction p).obj N) ≫ (adjunction p).counit.app N =
      (Mod.freeForgetAdjunction B).counit.app N := by
  have h := congrArg (fun f => π p ((restriction p).obj N) ≫ f) (counit_original p N)
  exact h.trans ((π_fromRestriction p (𝟙 ((restriction p).obj N))).trans
    ((Mod.freeForgetAdjunction B).homEquiv_symm_id N))

/-- The actual original induction maps preserve every generator component. -/
@[reassoc]
theorem generator_naturality {M M' : Mod C A} (f : M ⟶ M') :
    generator p M ≫ ((induction p).map f).hom = f.hom ≫ generator p M' := by
  have h := congrArg Mod.Hom.hom ((adjunction p).unit.naturality f)
  change f.hom ≫ ((adjunction p).unit.app M').hom =
    ((adjunction p).unit.app M).hom ≫ ((induction p).map f).hom at h
  exact ((congrArg (fun g => g ≫ ((induction p).map f).hom) (unit_hom p M)).symm.trans
    (h.symm.trans (congrArg (fun g => f.hom ≫ g) (unit_hom p M'))))

/-- Every original induction arrow is the same balanced descent of the full free-module arrow. -/
@[reassoc]
theorem π_induction_map {M M' : Mod C A} (f : M ⟶ M') :
    π p M ≫ (induction p).map f = (Mod.free B).map f.hom ≫ π p M' := by
  apply ((Mod.freeForgetAdjunction B).homEquiv M.X (object p M')).injective
  have hl : (Mod.freeForgetAdjunction B).homEquiv M.X (object p M')
      (π p M ≫ (induction p).map f) =
      generator p M ≫ ((induction p).map f).hom :=
    (freeHom_apply (object p M') (π p M ≫ (induction p).map f)).trans
      (Category.assoc _ _ _).symm
  have hr : (Mod.freeForgetAdjunction B).homEquiv M.X (object p M')
      ((Mod.free B).map f.hom ≫ π p M') = f.hom ≫ generator p M' :=
    ((Mod.freeForgetAdjunction B).homEquiv_naturality_left f.hom (π p M')).trans
      (congrArg (fun g => f.hom ≫ g) (freeHom_apply (object p M') (π p M')))
  exact hl.trans ((generator_naturality p f).trans hr.symm)

/-- The whole original forward Hom function is natural in every source module arrow. -/
theorem homEquiv_naturality_left {M M' : Mod C A} (f : M ⟶ M') (N : Mod C B)
    (h : object p M' ⟶ N) :
    homEquiv p M N ((induction p).map f ≫ h) = f ≫ homEquiv p M' N h := by
  exact (congrArg (fun e => e ((induction p).map f ≫ h)) (adjunction_homEquiv p M N)).symm.trans
    (((adjunction p).homEquiv_naturality_left f h).trans
      (congrArg (fun e => f ≫ e h) (adjunction_homEquiv p M' N)))

/-- Every whole original unit square uses the actual scalar restriction of the induction arrow. -/
theorem unit_naturality {M M' : Mod C A} (f : M ⟶ M') :
    f ≫ (adjunction p).unit.app M' =
      (adjunction p).unit.app M ≫ (restriction p).map ((induction p).map f) :=
  (adjunction p).unit.naturality f

/-- Every whole original counit square retains the full scalar-restriction arrow. -/
theorem counit_naturality {N N' : Mod C B} (f : N ⟶ N') :
    (induction p).map ((restriction p).map f) ≫ (adjunction p).counit.app N' =
      (adjunction p).counit.app N ≫ f := (adjunction p).counit.naturality f

/-- Both full triangle identities retain the original induction and restriction functors. -/
theorem triangles (M : Mod C A) (N : Mod C B) :
    (induction p).map ((adjunction p).unit.app M) ≫
      (adjunction p).counit.app ((induction p).obj M) = 𝟙 _ ∧
    (adjunction p).unit.app ((restriction p).obj N) ≫
      (restriction p).map ((adjunction p).counit.app N) = 𝟙 _ :=
  ⟨(adjunction p).left_triangle_components M, (adjunction p).right_triangle_components N⟩

end Coequalizers

section RelativeCarrier

variable [HasCoequalizers C]

/-- The complete original relative tensor carrier uses the scalar bimodule's actual right action. -/
def relativeTensorCarrier (M : Mod C A) : C :=
  coequalizer ((scalarBimodule p).actRight ▷ M.X)
    ((α_ B A M.X).hom ≫ (B ◁ M.mod.smul))

/-- The quotient projection for the actual relative tensor carrier. -/
def relativeTensorπ (M : Mod C A) : B ⊗ M.X ⟶ relativeTensorCarrier p M :=
  coequalizer.π ((scalarBimodule p).actRight ▷ M.X)
    ((α_ B A M.X).hom ≫ (B ◁ M.mod.smul))

end RelativeCarrier

section CarrierComparison

variable [HasColimitsOfSize.{0, 0} C]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]

omit [HasColimitsOfSize.{0, 0} C] [PreservesColimitsOfSize.{0, 0} (tensorLeft B)] in
/-- The associator identifies the forgotten free-module balancing pair with the relative tensor pair. -/
def carrierDiagramIso (M : Mod C A) :
    parallelPair ((Mod.forget B).map (rightMap p M)) ((Mod.forget B).map (leftMap M)) ≅
      parallelPair ((scalarBimodule p).actRight ▷ M.X)
        ((α_ B A M.X).hom ≫ (B ◁ M.mod.smul)) :=
  parallelPairIso (rightMap p M).hom (leftMap (B := B) M).hom
    ((scalarBimodule p).actRight ▷ M.X)
    ((α_ B A M.X).hom ≫ (B ◁ M.mod.smul))
    (α_ B A M.X).symm (Iso.refl (B ⊗ M.X))
    (by
      change (rightMap p M).hom ≫ (𝟙 (B ⊗ M.X)) =
        (α_ B A M.X).inv ≫ (rightAction p ▷ M.X)
      exact (Category.comp_id _).trans (rightMap_hom p M))
    (by
      change (B ◁ M.mod.smul) ≫ (𝟙 (B ⊗ M.X)) =
        (α_ B A M.X).inv ≫ (α_ B A M.X).hom ≫ (B ◁ M.mod.smul)
      simp only [Category.comp_id, Iso.inv_hom_id_assoc])

/-- The free-module coequalizer and the actual relative tensor have the same full native carrier. -/
def carrierIso (M : Mod C A) : (object p M).X ≅ relativeTensorCarrier p M := by
  letI : CreatesColimitsOfSize.{0, 0} (Mod.forget (D := C) B) := Mod.forgetCreatesColimits B
  exact (PreservesCoequalizer.iso (Mod.forget B) (rightMap p M) (leftMap M)).symm ≪≫
    HasColimit.isoOfNatIso (carrierDiagramIso p M)

/-- The carrier comparison sends the module quotient to the actual relative tensor quotient. -/
@[reassoc]
theorem π_carrierIso (M : Mod C A) :
    (π p M).hom ≫ (carrierIso p M).hom = relativeTensorπ p M := by
  let _ : CreatesColimitsOfSize.{0, 0} (Mod.forget (D := C) B) := Mod.forgetCreatesColimits B
  change (Mod.forget B).map (coequalizer.π (rightMap p M) (leftMap M)) ≫
      (PreservesCoequalizer.iso (Mod.forget B) (rightMap p M) (leftMap M)).inv ≫
        (HasColimit.isoOfNatIso (carrierDiagramIso p M)).hom = _
  rw [map_π_preserves_coequalizer_inv_assoc, HasColimit.ι_isoOfNatIso_hom]
  exact Category.id_comp _

end CarrierComparison
end CategoryTheory.Mod.ExtensionOfScalars
