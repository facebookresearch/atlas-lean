/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-!
# Parabolic sheaves with actual groupification weights

Weights and labelled arrows are the actual Grothendieck-group weight category.
All values are native quasi-coherent scheme modules. Periodicity uses actual
line tensors, unit/associativity diagrams and the given DF sections. Global
objects have explicit etale inverse-image comparisons, including their
identity, composition and period compatibility; they are not unrelated lists
of local filtrations. Nonintegral monoids retain distinct labelled arrows.

Reference: Borne--Vistoli, arXiv:1001.0466v2, Definitions5.2/5.8 and Theorem6.1.
Groupifying the actual DF line functor is an explicit construction dependency,
not an arbitrary coefficient lattice or an assumed root/parabolic equivalence.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
universe u

abbrev Groupification (P : CommMonCat.{u}) := Algebra.GrothendieckGroup P

def groupMap {P Q : CommMonCat.{u}} (f : P →* Q) : Groupification P →* Groupification Q :=
  Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp f)

@[simp] theorem groupMap_of {P Q : CommMonCat.{u}} (f : P →* Q) (p : P) :
    groupMap f (Algebra.GrothendieckGroup.of p) = Algebra.GrothendieckGroup.of (f p) := by
  exact congrArg (fun h : P →* Groupification Q => h p)
    (Algebra.GrothendieckGroup.lift.left_inv (Algebra.GrothendieckGroup.of.comp f))

/-- The actual functor on weights retains every monoid arrow label. -/
def weightMap {P Q : CommMonCat.{u}} (f : P →* Q) : Weight P ⥤ Weight Q where
  obj w := ⟨groupMap f w.value⟩
  map a := ⟨f a.label, by
    have h := congrArg (groupMap f) a.equation
    simpa only [map_mul, groupMap_of] using h⟩
  map_id w := by apply WeightHom.ext; exact f.map_one
  map_comp a b := by apply WeightHom.ext; exact f.map_mul _ _

def shift {P Q : CommMonCat.{u}} (j : P →* Q) (p : Groupification P) (w : Weight Q) :
    Weight Q := ⟨groupMap j p * w.value⟩

lemma shift_one {P Q : CommMonCat.{u}} (j : P →* Q) (w : Weight Q) : shift j 1 w = w := by
  apply Weight.ext; exact (by simp [shift])

lemma shift_mul {P Q : CommMonCat.{u}} (j : P →* Q) (p q : Groupification P)
    (w : Weight Q) : shift j (p*q) w = shift j p (shift j q w) := by
  apply Weight.ext; exact (by simp [shift, mul_assoc])

def shiftFunctor {P Q : CommMonCat.{u}} (j : P →* Q) (p : Groupification P) :
    Weight Q ⥤ Weight Q where
  obj w := shift j p w
  map {w v} a := ⟨a.label, by
    change Algebra.GrothendieckGroup.of a.label * (groupMap j p * w.value) = _
    rw [← mul_assoc, mul_comm (Algebra.GrothendieckGroup.of a.label), mul_assoc,
      a.equation]
    rfl⟩
  map_id _w := rfl
  map_comp _a _b := rfl

/-- The positive transition is the actual monoid label j(p). -/
def positiveArrow {P Q : CommMonCat.{u}} (j : P →* Q) (p : P) (w : Weight Q) :
    w ⟶ shift j (Algebra.GrothendieckGroup.of p) w :=
  ⟨j p, by
    change Algebra.GrothendieckGroup.of (j p) * w.value =
      groupMap j (Algebra.GrothendieckGroup.of p) * w.value
    rw [groupMap_of]⟩

/-- A strong symmetric line extension on the actual groupification, fixed
on all positive DF modules and all tensor/unit/associativity operations. -/
structure GroupifiedChart {X : Scheme.{u}} {P : CommMonCat.{u}}
    (D : DeligneFaltingsChart X P) where
  line : Groupification P → X.Modules
  invertible : ∀ p, IsLineBundle (line p)
  unit : line 1 ≅ structureModule X
  multiplication : ∀ p q, moduleTensor X (line p) (line q) ≅ line (p*q)
  positive : ∀ p : P, line (Algebra.GrothendieckGroup.of p) ≅ D.module p
  positive_unit : (positive 1).hom ≫ D.unit.hom =
    eqToHom (congrArg line (map_one Algebra.GrothendieckGroup.of)) ≫ unit.hom
  positive_multiplication : ∀ p q : P,
    tensorMap (positive p).hom (positive q).hom ≫ (D.multiplication p q).hom =
      (multiplication (Algebra.GrothendieckGroup.of p) (Algebra.GrothendieckGroup.of q)).hom ≫
        eqToHom (congrArg line (map_mul Algebra.GrothendieckGroup.of p q).symm) ≫
        (positive (p*q)).hom
  left_unit : ∀ p,
    (multiplication 1 p).hom ≫ eqToHom (congrArg line (one_mul p)) =
      tensorMap unit.hom (𝟙 (line p)) ≫ (tensorLeftUnit X (line p)).hom
  right_unit : ∀ p,
    (multiplication p 1).hom ≫ eqToHom (congrArg line (mul_one p)) =
      tensorMap (𝟙 (line p)) unit.hom ≫ (tensorRightUnit X (line p)).hom
  associativity : ∀ p q r,
    tripleLeft X (line p) (line q) (line r) ≫
      tensorMap (multiplication p q).hom (𝟙 (line r)) ≫ (multiplication (p*q) r).hom =
    tripleRight X (line p) (line q) (line r) ≫
      tensorMap (𝟙 (line p)) (multiplication q r).hom ≫ (multiplication p (q*r)).hom ≫
      eqToHom (congrArg line (mul_assoc p q r).symm)
  symmetry : ∀ p q,
    (multiplication p q).hom = (tensorSwap X (line p) (line q)).hom ≫
      (multiplication q p).hom ≫ eqToHom (congrArg line (mul_comm q p))

/-- Actual chartwise parabolic objects, including group periods and all
source section/unit/associativity normalizations. -/
structure LocalParabolic {X : Scheme.{u}} {P Q : CommMonCat.{u}}
    {D : DeligneFaltingsChart X P} (G : GroupifiedChart D) (j : P →* Q) where
  functor : Weight Q ⥤ X.Modules
  quasicoherent : ∀ w, SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (functor.obj w)
  periodic : ∀ p w, functor.obj (shift j p w) ≅ moduleTensor X (G.line p) (functor.obj w)
  periodic_naturality : ∀ p {w v} (a : w ⟶ v),
    functor.map ((shiftFunctor j p).map a) ≫ (periodic p v).hom =
      (periodic p w).hom ≫ tensorMap (𝟙 (G.line p)) (functor.map a)
  periodic_unit : ∀ w,
    (periodic 1 w).hom ≫ tensorMap G.unit.hom (𝟙 (functor.obj w)) ≫
      (tensorLeftUnit X (functor.obj w)).hom =
        eqToHom (congrArg functor.obj (shift_one j w))
  periodic_associativity : ∀ p q w,
    (periodic (p*q) w).hom =
      eqToHom (congrArg functor.obj (shift_mul j p q w)) ≫
      (periodic p (shift j q w)).hom ≫
      tensorMap (𝟙 (G.line p)) (periodic q w).hom ≫
      (tensorAssociator X (G.line p) (G.line q) (functor.obj w)).inv ≫
      tensorMap (G.multiplication p q).hom (𝟙 (functor.obj w))
  positive_transition : ∀ (p : P) w,
    functor.map (positiveArrow j p w) ≫ (periodic (Algebra.GrothendieckGroup.of p) w).hom ≫
      tensorMap (G.positive p).hom (𝟙 (functor.obj w)) =
    (tensorLeftUnit X (functor.obj w)).inv ≫ tensorMap (D.sectionMap p) (𝟙 (functor.obj w))

namespace LocalParabolic
variable {X : Scheme.{u}} {P Q : CommMonCat.{u}} {D : DeligneFaltingsChart X P}
    {G : GroupifiedChart D} {j : P →* Q}

structure Hom (E F : LocalParabolic G j) where
  map : E.functor ⟶ F.functor
  periodic : ∀ p w, (map.app (shift j p w)) ≫ (F.periodic p w).hom =
    (E.periodic p w).hom ≫ tensorMap (𝟙 (G.line p)) (map.app w)

@[ext] theorem Hom.ext {E F : LocalParabolic G j} {a b : Hom E F}
    (h : a.map = b.map) : a = b := by cases a; cases b; cases h; rfl

instance : Category (LocalParabolic G j) where
  Hom E F := Hom E F
  id E := ⟨𝟙 E.functor, by intros; simp⟩
  comp a b := ⟨a.map ≫ b.map, by
    intro p w
    change a.map.app _ ≫ b.map.app _ ≫ _ = _
    rw [b.periodic, ← Category.assoc, a.periodic]
    simp only [Category.assoc, ← tensorMap_comp, Category.id_comp]
    rfl⟩
  id_comp a := by apply Hom.ext; exact Category.id_comp _
  comp_id a := by apply Hom.ext; exact Category.comp_id _
  assoc a b c := by apply Hom.ext; exact Category.assoc _ _ _

end LocalParabolic

lemma groupMap_id (P : CommMonCat.{u}) :
    groupMap (MonoidHom.id P) = MonoidHom.id (Groupification P) := by
  apply (Algebra.GrothendieckGroup.lift (M := P) (G := Groupification P)).symm.injective
  ext p
  exact groupMap_of (MonoidHom.id P) p

lemma groupMap_comp {P Q R : CommMonCat.{u}} (f : Q →* R) (g : P →* Q) :
    groupMap (f.comp g) = (groupMap f).comp (groupMap g) := by
  apply (Algebra.GrothendieckGroup.lift (M := P) (G := Groupification R)).symm.injective
  ext p
  change groupMap (f.comp g) (Algebra.GrothendieckGroup.of p) =
    groupMap f (groupMap g (Algebra.GrothendieckGroup.of p))
  simp only [groupMap_of, MonoidHom.comp_apply]

lemma groupIdentity {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (p : Groupification (A.obj.obj (op U))) :
    groupMap (A.obj.map (𝟙 (op U))).hom p = p := by
  have h : (A.obj.map (𝟙 (op U))).hom = MonoidHom.id _ := by
    ext a; exact mapIdentity A U a
  rw [h, groupMap_id]
  rfl

lemma groupComposition {X : Scheme.{u}} (A : MonoidSheaf X)
    {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (p : Groupification (A.obj.obj (op U))) :
    groupMap (A.obj.map (g ≫ f).op).hom p =
      groupMap (A.obj.map g.op).hom (groupMap (A.obj.map f.op).hom p) := by
  rw [op_comp, A.obj.map_comp]
  change groupMap ((A.obj.map g.op).hom.comp (A.obj.map f.op).hom) p = _
  rw [groupMap_comp]
  rfl

lemma weightIdentity {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (w : Weight (A.obj.obj (op U))) :
    (weightMap (A.obj.map (𝟙 (op U))).hom).obj w = w := by
  apply Weight.ext
  exact groupIdentity A U w.value

lemma weightComposition {X : Scheme.{u}} (A : MonoidSheaf X)
    {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (w : Weight (A.obj.obj (op U))) :
    (weightMap (A.obj.map (g ≫ f).op).hom).obj w =
      (weightMap (A.obj.map g.op).hom).obj ((weightMap (A.obj.map f.op).hom).obj w) := by
  apply Weight.ext
  exact groupComposition A f g w.value

lemma weightPeriod {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B)
    {U V : X.Etale} (f : V ⟶ U) (p : Groupification (A.obj.obj (op U)))
    (w : Weight (B.obj.obj (op U))) :
    (weightMap (B.obj.map f.op).hom).obj (shift (j.hom.app (op U)).hom p w) =
      shift (j.hom.app (op V)).hom (groupMap (A.obj.map f.op).hom p)
        ((weightMap (B.obj.map f.op).hom).obj w) := by
  have hs : (B.obj.map f.op).hom.comp (j.hom.app (op U)).hom =
      (j.hom.app (op V)).hom.comp (A.obj.map f.op).hom := by
    ext a
    exact DenominatorRootFamilies.sheafMapNaturality j f a
  have h := congrArg groupMap hs
  rw [groupMap_comp, groupMap_comp] at h
  apply Weight.ext
  change groupMap (B.obj.map f.op).hom (groupMap (j.hom.app (op U)).hom p * w.value) = _
  rw [map_mul]
  have hp := congrArg (fun a => a p) h
  exact congrArg (fun a => a * groupMap (B.obj.map f.op).hom w.value) hp

/-- The line groupification extends the actual cartesian DF functor, with
its full etale inverse-image coherence and generator normalization. -/
structure GroupifiedDF {X : Scheme.{u}} {A : MonoidSheaf X} (D : Structure A) where
  chart : ∀ U : X.Etale, GroupifiedChart (D.chart U)
  reindex : ∀ {U V : X.Etale} (f : V ⟶ U) (p : Groupification (A.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).obj ((chart U).line p) ≅
      (chart V).line (groupMap (A.obj.map f.op).hom p)
  positive : ∀ {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback f.left).map ((chart U).positive a).hom ≫ (D.reindex f a).hom =
      (reindex f (Algebra.GrothendieckGroup.of a)).hom ≫
        eqToHom (congrArg ((chart V).line) (groupMap_of (A.obj.map f.op).hom a)) ≫
        ((chart V).positive (A.obj.map f.op a)).hom
  unit : ∀ {U V : X.Etale} (f : V ⟶ U),
    (reindex f 1).hom ≫ eqToHom (congrArg ((chart V).line)
      (map_one (groupMap (A.obj.map f.op).hom))) ≫ (chart V).unit.hom =
      (Scheme.Modules.pullback f.left).map (chart U).unit.hom ≫
        SheafOfModules.pullbackObjUnitToUnit f.left.toRingCatSheafHom
  multiplication : ∀ {U V : X.Etale} (f : V ⟶ U) (p q : Groupification (A.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).map ((chart U).multiplication p q).hom ≫
      (reindex f (p*q)).hom =
    ((D.tensorPullback f).comparison ((chart U).line p) ((chart U).line q)).hom ≫
      tensorMap (reindex f p).hom (reindex f q).hom ≫
      ((chart V).multiplication (groupMap (A.obj.map f.op).hom p)
        (groupMap (A.obj.map f.op).hom q)).hom ≫
      eqToHom (congrArg ((chart V).line) (map_mul (groupMap (A.obj.map f.op).hom) p q).symm)
  identity : ∀ (U : X.Etale) (p : Groupification (A.obj.obj (op U))),
    (reindex (𝟙 U) p).hom ≫ eqToHom (congrArg ((chart U).line) (groupIdentity A U p)) =
      (Scheme.Modules.pullbackId U.left).hom.app ((chart U).line p)
  composition : ∀ {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (p : Groupification (A.obj.obj (op U))),
    (reindex (g ≫ f) p).hom =
      (Scheme.Modules.pullbackComp g.left f.left).inv.app ((chart U).line p) ≫
      (Scheme.Modules.pullback g.left).map (reindex f p).hom ≫
      (reindex g (groupMap (A.obj.map f.op).hom p)).hom ≫
      eqToHom (congrArg ((chart W).line) (groupComposition A f g p).symm)

/-- General sheaf-denominator parabolic objects. The etale descent maps
are actual scheme-module pullbacks, with all period/cocycle comparisons. -/
structure Parabolic {X : Scheme.{u}} {A B : MonoidSheaf X} {D : Structure A}
    (G : GroupifiedDF D) (j : A ⟶ B) where
  localObject : ∀ U : X.Etale, LocalParabolic (G.chart U) (j.hom.app (op U)).hom
  reindex : ∀ {U V : X.Etale} (f : V ⟶ U),
    (localObject U).functor ⋙ Scheme.Modules.pullback f.left ≅
      weightMap (B.obj.map f.op).hom ⋙ (localObject V).functor
  identity : ∀ (U : X.Etale) (w : Weight (B.obj.obj (op U))),
    (reindex (𝟙 U)).hom.app w ≫
      eqToHom (congrArg (localObject U).functor.obj (weightIdentity B U w)) =
        (Scheme.Modules.pullbackId U.left).hom.app ((localObject U).functor.obj w)
  composition : ∀ {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (w : Weight (B.obj.obj (op U))),
    (reindex (g ≫ f)).hom.app w =
      (Scheme.Modules.pullbackComp g.left f.left).inv.app ((localObject U).functor.obj w) ≫
      (Scheme.Modules.pullback g.left).map ((reindex f).hom.app w) ≫
      (reindex g).hom.app ((weightMap (B.obj.map f.op).hom).obj w) ≫
      eqToHom (congrArg (localObject W).functor.obj (weightComposition B f g w).symm)
  period_compatibility : ∀ {U V : X.Etale} (f : V ⟶ U)
    (p : Groupification (A.obj.obj (op U))) (w : Weight (B.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).map ((localObject U).periodic p w).hom ≫
      ((D.tensorPullback f).comparison ((G.chart U).line p) ((localObject U).functor.obj w)).hom ≫
      tensorMap (G.reindex f p).hom ((reindex f).hom.app w) =
    (reindex f).hom.app (shift (j.hom.app (op U)).hom p w) ≫
      eqToHom (congrArg (localObject V).functor.obj (weightPeriod j f p w)) ≫
      ((localObject V).periodic (groupMap (A.obj.map f.op).hom p)
        ((weightMap (B.obj.map f.op).hom).obj w)).hom

namespace Parabolic
variable {X : Scheme.{u}} {A B : MonoidSheaf X} {D : Structure A}
    {G : GroupifiedDF D} {j : A ⟶ B}

structure Hom (E F : Parabolic G j) where
  localMap : ∀ U : X.Etale, E.localObject U ⟶ F.localObject U
  reindexing : ∀ {U V : X.Etale} (f : V ⟶ U) (w : Weight (B.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).map ((localMap U).map.app w) ≫ (F.reindex f).hom.app w =
      (E.reindex f).hom.app w ≫ (localMap V).map.app ((weightMap (B.obj.map f.op).hom).obj w)

@[ext] theorem Hom.ext {E F : Parabolic G j} {a b : Hom E F}
    (h : ∀ U, a.localMap U = b.localMap U) : a = b := by
  cases a; cases b; congr
  exact funext h

instance : Category (Parabolic G j) where
  Hom E F := Hom E F
  id E := ⟨fun _U => 𝟙 _, by
    intro U V f w
    change (Scheme.Modules.pullback f.left).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    simp⟩
  comp a b := ⟨fun U => a.localMap U ≫ b.localMap U, by
    intro U V f w
    change (Scheme.Modules.pullback f.left).map
      ((a.localMap U).map.app w ≫ (b.localMap U).map.app w) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, b.reindexing, ← Category.assoc, a.reindexing]
    exact Category.assoc _ _ _⟩
  id_comp a := by apply Hom.ext; intro U; exact Category.id_comp _
  comp_id a := by apply Hom.ext; intro U; exact Category.comp_id _
  assoc a b c := by apply Hom.ext; intro U; exact Category.assoc _ _ _

end Parabolic
end MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
