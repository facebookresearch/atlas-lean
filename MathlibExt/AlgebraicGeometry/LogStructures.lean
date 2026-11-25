/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CommMonoidColimits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Log structures on actual ringed Grothendieck sites

The ringed site consists of a native Grothendieck topology and a sheaf of
commutative rings. A prelog structure is an actual commutative-monoid sheaf
map into the multiplicative structure sheaf. The log condition says that
its actual pullback over the unit sheaf maps isomorphically to that unit
sheaf. Its characteristic is the actual sheaf pushout killing these units.

Charts are normalized constant-monoid maps whose unit square is a pushout.
Local charts use Mathlib's actual slice topology `J.over U`; fine and fs
conditions require covering families of such charts, rather than only a
pointwise finiteness label. Integral and saturated monoids are tested in
their actual Grothendieck group. No log-smoothness criterion or geometric
existence result is asserted by these definitions.

References: Kato, *Logarithmic structures of Fontaine--Illusie*, §1;
Nakayama--Ogus, *Relative rounding in toric and logarithmic geometry*,
Definition 3.4 and its associated-log/chart construction; Achinger--Ogus,
https://arxiv.org/abs/1802.02234, §3.1. Generic sheafification, monoid limits,
slice restriction and site-point fibers reuse Mathlib's proved operations.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogStructures

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

abbrev RingSheaf := Sheaf J CommRingCat.{max u v}
abbrev MonoidSheaf := Sheaf J CommMonCat.{max u v}

/-- Forget only the additive ring operations, retaining multiplication. -/
abbrev ringMonoidsFunctor : RingSheaf J ⥤ MonoidSheaf J :=
  sheafCompose J (forget₂ CommRingCat CommMonCat)

abbrev ringMonoids (O : RingSheaf J) : MonoidSheaf J :=
  (ringMonoidsFunctor J).obj O

abbrev unitFunctor : CommMonCat.{w} ⥤ CommMonCat.{w} :=
  CommMonCat.units ⋙ forget₂ CommGrpCat CommMonCat

/-- The actual sheaf of units of the specified structure sheaf. -/
abbrev units (O : RingSheaf J) : MonoidSheaf J :=
  (sheafCompose J unitFunctor.{max u v}).obj (ringMonoids J O)

/-- The canonical inclusion of units, computed section by section. -/
def unitInclusion (O : RingSheaf J) : units J O ⟶ ringMonoids J O where
  hom :=
    { app U := CommMonCat.ofHom (Units.coeHom ((ringMonoids J O).obj.obj U))
      naturality _ _ _ := by ext x; rfl }

instance unitInclusion_mono (O : RingSheaf J) : Mono (unitInclusion J O) := by
  have (U : Cᵒᵖ) : Mono ((unitInclusion J O).hom.app U) :=
    ConcreteCategory.mono_of_injective _ Units.val_injective
  have : Mono (unitInclusion J O).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono J CommMonCat (unitInclusion J O)

/-- A native prelog structure, as an object over the structure monoid sheaf. -/
abbrev Prelog (O : RingSheaf J) := Over (ringMonoids J O)

/-- The actual inverse image of the unit sheaf under a prelog map. -/
abbrev inverseUnits {O : RingSheaf J} (P : Prelog J O) : MonoidSheaf J :=
  pullback P.hom (unitInclusion J O)

abbrev unitRestriction {O : RingSheaf J} (P : Prelog J O) :
    inverseUnits J P ⟶ units J O :=
  pullback.snd P.hom (unitInclusion J O)

/-- The log condition is the isomorphism of this computed unit pullback. -/
def isLog (O : RingSheaf J) : ObjectProperty (Prelog J O) :=
  fun P => IsIso (unitRestriction J P)

/-- General log structures on this actual ringed site. Morphisms are the
native commuting triangles of monoid sheaf maps over its ring sheaf. -/
abbrev LogStructure (O : RingSheaf J) := (isLog J O).FullSubcategory

/-- The actual trivial log structure has monoid sheaf O*. -/
def trivialLog (O : RingSheaf J) : LogStructure J O := by
  refine ⟨Over.mk (unitInclusion J O), ?_⟩
  change IsIso (pullback.snd (unitInclusion J O) (unitInclusion J O))
  have h : pullback.fst (unitInclusion J O) (unitInclusion J O) =
      pullback.snd (unitInclusion J O) (unitInclusion J O) :=
    (cancel_mono (unitInclusion J O)).1 pullback.condition
  refine ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
      exact h.symm
    · simp
  · simp

abbrev monoid {O : RingSheaf J} (L : LogStructure J O) : MonoidSheaf J := L.obj.left
abbrev alpha {O : RingSheaf J} (L : LogStructure J O) :
    monoid J L ⟶ ringMonoids J O := L.obj.hom

/-- The unit map is forced by the log condition, not chosen independently. -/
def unitMap {O : RingSheaf J} (L : LogStructure J O) : units J O ⟶ monoid J L :=
  letI : IsIso (unitRestriction J L.obj) := L.property
  inv (unitRestriction J L.obj) ≫ pullback.fst L.obj.hom (unitInclusion J O)

theorem unitMap_alpha {O : RingSheaf J} (L : LogStructure J O) :
    unitMap J L ≫ alpha J L = unitInclusion J O := by
  let : IsIso (unitRestriction J L.obj) := L.property
  simp only [unitMap, alpha, Category.assoc]
  rw [pullback.condition, ← Category.assoc]
  change (inv (unitRestriction J L.obj) ≫ unitRestriction J L.obj) ≫
    unitInclusion J O = unitInclusion J O
  rw [IsIso.inv_hom_id, Category.id_comp]

/-- A map into the unit pullback factors through the forced unit map. -/
theorem factorThroughUnits {O : RingSheaf J} (L : LogStructure J O)
    {T : MonoidSheaf J} (a : T ⟶ monoid J L) (b : T ⟶ units J O)
    (w : a ≫ alpha J L = b ≫ unitInclusion J O) : a = b ≫ unitMap J L := by
  let : IsIso (unitRestriction J L.obj) := L.property
  have h : pullback.lift a b w = b ≫ inv (unitRestriction J L.obj) := by
    apply (cancel_mono (unitRestriction J L.obj)).1
    simp [unitRestriction, Category.assoc]
  calc
    a = pullback.lift a b w ≫ pullback.fst L.obj.hom (unitInclusion J O) :=
      (pullback.lift_fst ..).symm
    _ = b ≫ unitMap J L := by rw [h]; rfl

/-- The actual characteristic quotient sheaf `M / O*`. -/
def characteristic {O : RingSheaf J} (L : LogStructure J O) : MonoidSheaf J :=
  pushout (unitMap J L) (terminal.from (units J O))

def characteristicMap {O : RingSheaf J} (L : LogStructure J O) :
    monoid J L ⟶ characteristic J L :=
  pushout.inl _ _

theorem characteristic_unit {O : RingSheaf J} (L : LogStructure J O) :
    unitMap J L ≫ characteristicMap J L =
      terminal.from (units J O) ≫ pushout.inr (unitMap J L) (terminal.from (units J O)) :=
  pushout.condition

/-- The fixed associated-prelog candidate is the sheaf pushout along units. -/
def associatedPrelog {O : RingSheaf J} (P : Prelog J O) : Prelog J O :=
  Over.mk (pushout.desc P.hom (unitInclusion J O) (pullback.condition ..))

def toAssociated {O : RingSheaf J} (P : Prelog J O) : P ⟶ associatedPrelog J P :=
  Over.homMk (pushout.inl _ _) (pushout.inl_desc ..)

/-- The canonical map out of logification uses the actual pushout universal
property and the target's forced unit map. -/
def associatedMap {O : RingSheaf J} {P : Prelog J O} (L : LogStructure J O)
    (f : P ⟶ L.obj) : associatedPrelog J P ⟶ L.obj :=
  let h := factorThroughUnits J L
    (pullback.fst P.hom (unitInclusion J O) ≫ f.left)
    (pullback.snd P.hom (unitInclusion J O)) (by
      change (pullback.fst P.hom (unitInclusion J O) ≫ f.left) ≫ L.obj.hom = _
      rw [Category.assoc, f.w]
      exact pullback.condition)
  Over.homMk (pushout.desc f.left (unitMap J L) h) (by
    apply pushout.hom_ext
    · simp [associatedPrelog, f.w]
    · simp [associatedPrelog, unitMap_alpha])

theorem toAssociated_associatedMap {O : RingSheaf J} {P : Prelog J O}
    (L : LogStructure J O) (f : P ⟶ L.obj) :
    toAssociated J P ≫ associatedMap J L f = f := by
  apply (Over.forget (ringMonoids J O)).map_injective
  change pushout.inl _ _ ≫ pushout.desc f.left (unitMap J L) _ = f.left
  exact pushout.inl_desc ..

/-- Changing the ring map uses the actual functor on over categories. -/
abbrev changeRing {O O' : RingSheaf J} (f : O ⟶ O') : Prelog J O ⥤ Prelog J O' :=
  Over.map ((ringMonoidsFunctor J).map f)

/-- A log morphism over a fixed ring-sheaf map is an actual compatible
monoid-sheaf map. The source and target log conditions remain separate. -/
abbrev HomOver {O O' : RingSheaf J} (f : O ⟶ O')
    (L : LogStructure J O) (L' : LogStructure J O') :=
  ((changeRing J f).obj L.obj ⟶ L'.obj)

section Monoids

/-- Integral means injective into the actual groupification. -/
def IsIntegralMonoid (P : CommMonCat.{w}) : Prop :=
  Function.Injective (Algebra.GrothendieckGroup.of (M := P))

def IsFineMonoid (P : CommMonCat.{w}) : Prop := IsIntegralMonoid P ∧ IsMulFG P

/-- The raw root-closure condition in the actual groupification. -/
def IsRootClosedMonoid (P : CommMonCat.{w}) : Prop :=
  ∀ (g : Algebra.GrothendieckGroup P) (n : ℕ), 0 < n →
    (∃ p : P, Algebra.GrothendieckGroup.of p = g ^ n) →
      ∃ p : P, Algebra.GrothendieckGroup.of p = g

/-- Saturation includes integrality, as in the standard log vocabulary. -/
def IsSaturatedMonoid (P : CommMonCat.{w}) : Prop :=
  IsIntegralMonoid P ∧ IsRootClosedMonoid P

def IsFineSaturatedMonoid (P : CommMonCat.{w}) : Prop :=
  IsFineMonoid P ∧ IsSaturatedMonoid P

def IsSharpMonoid (P : CommMonCat.{w}) : Prop := ∀ p : P, IsUnit p → p = 1

def groupMap {P Q : CommMonCat.{w}} (f : P ⟶ Q) :
    Algebra.GrothendieckGroup P →* Algebra.GrothendieckGroup Q :=
  Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp f.hom)

/-- Exactness is the native Cartesian groupification square. -/
def IsExactMonoidMap {P Q : CommMonCat.{w}} (f : P ⟶ Q) : Prop :=
  IsPullback f (CommMonCat.ofHom (Algebra.GrothendieckGroup.of (M := P)))
    (CommMonCat.ofHom (Algebra.GrothendieckGroup.of (M := Q)))
    (CommMonCat.ofHom (groupMap f))

def IsKummerMonoidMap {P Q : CommMonCat.{w}} (f : P ⟶ Q) : Prop :=
  Function.Injective f ∧ ∀ q : Q, ∃ n : ℕ, 0 < n ∧ ∃ p : P, f p = q ^ n

def IsLocalMonoidMap {P Q : CommMonCat.{w}} (f : P ⟶ Q) : Prop :=
  ∀ p : P, IsUnit (f p) ↔ IsUnit p

/-- Kill the actual unit group of a monoid by a native pushout. -/
def monoidCharacteristic (P : CommMonCat.{w}) : CommMonCat.{w} :=
  pushout (CommGrpCat.forget₂CommMonAdj.counit.app P)
    (terminal.from (unitFunctor.obj P))

def monoidCharacteristicProjection (P : CommMonCat.{w}) : P ⟶ monoidCharacteristic P :=
  pushout.inl _ _

/-- The induced map of characteristic monoids is the actual pushout map. -/
def monoidCharacteristicMap {P Q : CommMonCat.{w}} (f : P ⟶ Q) :
    monoidCharacteristic P ⟶ monoidCharacteristic Q :=
  pushout.map (CommGrpCat.forget₂CommMonAdj.counit.app P)
    (terminal.from (unitFunctor.obj P))
    (CommGrpCat.forget₂CommMonAdj.counit.app Q)
    (terminal.from (unitFunctor.obj Q))
    f (𝟙 _) (unitFunctor.map f)
    (by simpa only [Functor.id_map] using
      (CommGrpCat.forget₂CommMonAdj.counit.naturality f).symm)
    (by apply terminal.hom_ext)

end Monoids

/-- A chart on the actual slice site. The pushout square is precisely
logification of its constant-monoid prelog map on that slice. -/
structure Chart {O : RingSheaf J} (L : LogStructure J O) (U : C)
    (P : CommMonCat.{max u v}) where
  map : (constantSheaf (J.over U) CommMonCat).obj P ⟶
    (J.overPullback CommMonCat U).obj (monoid J L)
  pushout : IsPushout
    (pullback.fst
      (map ≫ (J.overPullback CommMonCat U).map (alpha J L))
      ((J.overPullback CommMonCat U).map (unitInclusion J O)))
    (pullback.snd
      (map ≫ (J.overPullback CommMonCat U).map (alpha J L))
      ((J.overPullback CommMonCat U).map (unitInclusion J O)))
    map ((J.overPullback CommMonCat U).map (unitMap J L))

/-- Actual covering-family charts, with a specified native monoid property. -/
def HasCharts {O : RingSheaf J} (L : LogStructure J O)
    (condition : CommMonCat.{max u v} → Prop) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.generate (Presieve.ofArrows V f) ∈ J U ∧
      ∀ i, ∃ P : CommMonCat.{max u v}, condition P ∧ Nonempty (Chart J L (V i) P)

def HasFineCharts {O : RingSheaf J} (L : LogStructure J O) : Prop :=
  HasCharts J L IsFineMonoid

def HasFineSaturatedCharts {O : RingSheaf J} (L : LogStructure J O) : Prop :=
  HasCharts J L IsFineSaturatedMonoid

/-- The characteristic monoid at an actual site point, not a free fiber. -/
abbrev characteristicAt {O : RingSheaf J} (L : LogStructure J O)
    (p : J.Point.{max u v}) : CommMonCat.{max u v} :=
  (p.sheafFiber (A := CommMonCat)).obj (characteristic J L)

abbrev rawCharacteristicAt {O : RingSheaf J} (L : LogStructure J O)
    (p : J.Point.{max u v}) : CommMonCat.{max u v} :=
  monoidCharacteristic ((p.sheafFiber (A := CommMonCat)).obj (monoid J L))

/-- A comparison, at a point $p$ of the site, of the two characteristic monoids of the log
structure $L$ with monoid sheaf $M$: an isomorphism (`iso`) from $M_p / M_p^\times$, the fibre of
$M$ at $p$ modulo its units, to the fibre at $p$ of the characteristic sheaf
$\overline{M} = M / \mathcal{O}^\times$, such that the projection $M_p \to M_p / M_p^\times$
followed by this isomorphism is the fibre at $p$ of the quotient map $M \to \overline{M}$
(`normalized`). -/
structure CharacteristicFiberComparison {O : RingSheaf J} (L : LogStructure J O)
    (p : J.Point.{max u v}) where
  iso : rawCharacteristicAt J L p ≅ characteristicAt J L p
  normalized : monoidCharacteristicProjection
      ((p.sheafFiber (A := CommMonCat)).obj (monoid J L)) ≫ iso.hom =
    (p.sheafFiber (A := CommMonCat)).map (characteristicMap J L)

section SiteMorphisms

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
  (F : D ⥤ C) [F.IsContinuous K J]

/-- Restriction along an actual continuous functor commutes with forgetting
the ring's additive operations. Both sides have the same section maps. -/
def pushRingMonoidsIso (O : RingSheaf J) :
    ringMonoids K ((F.sheafPushforwardContinuous CommRingCat K J).obj O) ≅
      (F.sheafPushforwardContinuous CommMonCat K J).obj (ringMonoids J O) :=
  Iso.refl _

/-- Log morphisms on different ringed sites. The continuous site functor,
ring structure map and monoid-map commuting triangle are all actual maps.
This allows small-étale as well as Zariski realizations. -/
abbrev HomAlong {O : RingSheaf J} {O' : RingSheaf K}
    (sharp : O' ⟶ (F.sheafPushforwardContinuous CommRingCat K J).obj O)
    (L : LogStructure J O) (L' : LogStructure K O') :=
  ((Over.map ((ringMonoidsFunctor K).map sharp ≫
      (pushRingMonoidsIso J K F O).hom)).obj L'.obj ⟶
    Over.mk ((F.sheafPushforwardContinuous CommMonCat K J).map (alpha J L)))

end SiteMorphisms

section Schemes

open _root_.AlgebraicGeometry TopCat TopologicalSpace

universe z

abbrev zariskiSite (X : Scheme.{z}) := Opens.grothendieckTopology X
abbrev ZariskiLogStructure (X : Scheme.{z}) := LogStructure (zariskiSite X) X.sheaf

/-- A scheme carrying an actual log structure on its Zariski ringed site.
This is a specialization of the general ringed-site contracts above. -/
structure ZariskiLogScheme where
  scheme : Scheme.{z}
  log : ZariskiLogStructure scheme

abbrev schemeMonoidSpace : Scheme.{z} ⥤ PresheafedSpace CommMonCat.{z} :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace ⋙
      (forget₂ CommRingCat CommMonCat).mapPresheaf

def logSpace (X : ZariskiLogScheme.{z}) : PresheafedSpace CommMonCat.{z} where
  carrier := X.scheme.carrier
  presheaf := (monoid (zariskiSite X.scheme) X.log).obj

/-- The prelog structure map, with identity on the actual underlying space. -/
def alphaSpace (X : ZariskiLogScheme.{z}) :
    (schemeMonoidSpace.obj X.scheme) ⟶ logSpace X where
  base := 𝟙 X.scheme.carrier
  c := (alpha (zariskiSite X.scheme) X.log).hom ≫
    eqToHom (Presheaf.Pushforward.id_eq _).symm

namespace ZariskiLogScheme

/-- An actual scheme map and compatible monoid-sheaf map. The commuting
square also forces equality of their underlying continuous maps. -/
structure Hom (X Y : ZariskiLogScheme.{z}) where
  schemeMap : X.scheme ⟶ Y.scheme
  logMap : logSpace X ⟶ logSpace Y
  compatibility : alphaSpace X ≫ logMap = schemeMonoidSpace.map schemeMap ≫ alphaSpace Y

@[ext] theorem Hom.ext {X Y : ZariskiLogScheme.{z}} {f g : Hom X Y}
    (h : f.schemeMap = g.schemeMap) (h' : f.logMap = g.logMap) : f = g := by
  cases f
  cases g
  cases h
  cases h'
  rfl

def id (X : ZariskiLogScheme.{z}) : Hom X X where
  schemeMap := 𝟙 X.scheme
  logMap := 𝟙 (logSpace X)
  compatibility := by
    rw [_root_.CategoryTheory.Functor.map_id]
    simp only [Category.comp_id, Category.id_comp]

def comp {X Y Z : ZariskiLogScheme.{z}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  schemeMap := f.schemeMap ≫ g.schemeMap
  logMap := f.logMap ≫ g.logMap
  compatibility := by
    rw [Functor.map_comp]
    calc
      alphaSpace X ≫ (f.logMap ≫ g.logMap) =
          (schemeMonoidSpace.map f.schemeMap ≫ alphaSpace Y) ≫ g.logMap := by
            rw [← Category.assoc, f.compatibility]
      _ = (schemeMonoidSpace.map f.schemeMap ≫ schemeMonoidSpace.map g.schemeMap) ≫
          alphaSpace Z := by rw [Category.assoc, g.compatibility, Category.assoc]

instance : Category ZariskiLogScheme.{z} where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by apply Hom.ext <;> simp [id, comp]
  comp_id f := by apply Hom.ext <;> simp [id, comp]
  assoc f g h := by apply Hom.ext <;> simp [comp, Category.assoc]

theorem underlying_map {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) :
    f.logMap.base = f.schemeMap.base := by
  have h := congrArg
    (fun a : schemeMonoidSpace.obj X.scheme ⟶ logSpace Y => a.base) f.compatibility
  change (𝟙 X.scheme.carrier) ≫ f.logMap.base =
    f.schemeMap.base ≫ (𝟙 Y.scheme.carrier) at h
  simpa [logSpace] using h

/-- The actual direct-image log map with the scheme's underlying map fixed. -/
def logSharp {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) :
    monoid (zariskiSite Y.scheme) Y.log ⟶
      (TopCat.Sheaf.pushforward CommMonCat f.schemeMap.base).obj
        (monoid (zariskiSite X.scheme) X.log) := by
  refine ObjectProperty.homMk ?_
  change (logSpace Y).presheaf ⟶
    (TopCat.Presheaf.pushforward CommMonCat f.schemeMap.base).obj (logSpace X).presheaf
  rw [← underlying_map f]
  exact f.logMap.c

/-- Inverse image is the actual mate under the sheaf pullback adjunction. -/
def inverseImageMap {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback CommMonCat f.schemeMap.base).obj
      (monoid (zariskiSite Y.scheme) Y.log) ⟶ monoid (zariskiSite X.scheme) X.log :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommMonCat f.schemeMap.base).homEquiv _ _).symm
    (logSharp f)

def inverseImagePrelog {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) :
    Prelog (zariskiSite X.scheme) X.scheme.sheaf :=
  Over.mk (inverseImageMap f ≫ alpha (zariskiSite X.scheme) X.log)

/-- The full associated inverse-image comparison, fixed by the actual mate
and logification pushout. This works for nonintegral log structures too. -/
def inverseImageComparison {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) :
    associatedPrelog (zariskiSite X.scheme) (inverseImagePrelog f) ⟶ X.log.obj :=
  associatedMap (zariskiSite X.scheme) X.log
    (Over.homMk (inverseImageMap f) rfl)

/-- Exactness uses the actual induced map of log-monoid stalks. -/
def IsExact {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, IsExactMonoidMap (f.logMap.stalkMap x)

/-- Kummerness is tested on the actual sharp characteristic stalk map. -/
def IsKummer {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, IsKummerMonoidMap (monoidCharacteristicMap (f.logMap.stalkMap x))

def CharacteristicIsomorphism {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) : Prop :=
  ∀ x : X.scheme, IsIso (monoidCharacteristicMap (f.logMap.stalkMap x))

/-- Strictness means the full associated inverse image is isomorphic to M_X.
Characteristic isomorphism alone is insufficient without integrality. -/
def IsStrict {X Y : ZariskiLogScheme.{z}} (f : X ⟶ Y) : Prop :=
  IsIso (inverseImageComparison f).left

/-- The actual underlying-scheme functor. -/
def forgetToScheme : ZariskiLogScheme.{z} ⥤ Scheme.{z} where
  obj X := X.scheme
  map f := f.schemeMap

end ZariskiLogScheme

end Schemes

end MathlibExt.AlgebraicGeometry.LogStructures
