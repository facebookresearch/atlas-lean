/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogStructures

import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.GroupTheory.Congruence.Basic

/-!
# Fine characteristic monoids at site points

Local fine charts give fine and sharp fibers of the characteristic sheaf
of a log structure on a ringed Grothendieck site.

Sources: Kato, *Logarithmic structures of Fontaine--Illusie*, §1;
Nakayama--Ogus, *Relative rounding in toric and logarithmic geometry*,
Definition 3.4 and the following associated-log/chart construction,
https://math.berkeley.edu/~ogus/preprints/nakayamaogus.pdf;
Achinger--Ogus, *Monodromy and log geometry*, §3.1,
https://arxiv.org/abs/1802.02234.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.LogStructures
open CategoryTheory.Limits Opposite

universe u v
universe w


private instance monoidAB5 : AB5 CommMonCat.{w} where
  ofShape D _ _ := by
    let : PreservesFiniteLimits
        (colim (J := D) (C := CommMonCat.{w}) ⋙ forget CommMonCat.{w}) :=
      preservesFiniteLimits_of_natIso (preservesColimitNatIso (forget CommMonCat.{w})).symm
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (forget CommMonCat.{w})⟩

private abbrev Gover {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (p : J.Point.{max u v}) {V : C}
    (xV : p.fiber.obj V) : (p.over xV).fiber.Elements ⥤ p.fiber.Elements where
  obj e := p.fiber.elementsMk e.obj.left e.val.val
  map f := Functor.Elements.homMk f.hom.left (Subtype.ext_iff.mp f.map_val)

private instance Gover_initial {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (p : J.Point.{max u v}) {V : C}
    (xV : p.fiber.obj V) : Functor.Initial (Gover J p xV) := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    let W := IsCofiltered.min (p.fiber.elementsMk V xV) d
    let e : W ⟶ p.fiber.elementsMk V xV := IsCofiltered.minToLeft _ _
    let f : W ⟶ d := IsCofiltered.minToRight _ _
    let z : (p.over xV).fiber.obj (Over.mk e.hom) :=
      ⟨W.val, (FunctorToTypes.mem_fromOverSubfunctor_iff p.fiber xV
        (U := Over.mk e.hom) W.val).mpr e.map_val⟩
    exact ⟨(p.over xV).fiber.elementsMk (Over.mk e.hom) z, ⟨f⟩⟩
  · intro d c s s'
    let e := IsCofiltered.eqHom s s'
    let c' := (p.over xV).fiber.elementsMk (Over.mk (e.hom ≫ c.obj.hom))
      ⟨(IsCofiltered.eq s s').val, by
        rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
        have hc := c.val.property
        rw [FunctorToTypes.mem_fromOverSubfunctor_iff] at hc
        simpa [Functor.map_comp, e.map_val] using hc⟩
    refine ⟨c', Functor.Elements.homMk (Over.homMk e.hom)
      (by apply Subtype.ext; exact e.map_val), ?_⟩
    exact IsCofiltered.eq_condition s s'

private def overFiberIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (p : J.Point.{max u v}) {V : C}
    (xV : p.fiber.obj V) (F : Sheaf J CommMonCat.{max u v}) :
    (p.over xV).sheafFiber.obj ((J.overPullback CommMonCat V).obj F) ≅
      p.sheafFiber.obj F :=
  Functor.Final.colimitIso (Gover J p xV).op ((Functor.Elements.π p.fiber).op ⋙ F.obj)

private def presheafConstFiberIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (p : J.Point.{max u v}) (P : CommMonCat.{max u v}) :
    p.presheafFiber.obj ((Functor.const Cᵒᵖ).obj P) ≅ P :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (isColimitConstCocone p.fiber.Elementsᵒᵖ P)

private def sheafConstFiberIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (p : J.Point.{max u v}) (P : CommMonCat.{max u v}) :
    p.sheafFiber.obj ((constantSheaf J CommMonCat).obj P) ≅ P :=
  (asIso (p.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj P)))).symm ≪≫
    presheafConstFiberIso J p P

private def quotCon {P K : CommMonCat.{w}} (a : K ⟶ P) : Con P where
  r p q := ∃ k k' : K, p * a k = q * a k'
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, 1, rfl⟩
    · rintro p q ⟨k, k', h⟩
      exact ⟨k', k, h.symm⟩
    · rintro p q r ⟨k₁, k₁', h₁⟩ ⟨k₂, k₂', h₂⟩
      refine ⟨k₁ * k₂, k₂' * k₁', ?_⟩
      simp only [map_mul]
      calc
        p * (a k₁ * a k₂) = (p * a k₁) * a k₂ := (mul_assoc ..).symm
        _ = (q * a k₁') * a k₂ := congrArg (· * a k₂) h₁
        _ = (q * a k₂) * a k₁' := by ac_rfl
        _ = (r * a k₂') * a k₁' := congrArg (· * a k₁') h₂
        _ = r * (a k₂' * a k₁') := mul_assoc ..
  mul' := by
    rintro p q r s ⟨k₁, k₁', h₁⟩ ⟨k₂, k₂', h₂⟩
    refine ⟨k₁ * k₂, k₁' * k₂', ?_⟩
    simp only [map_mul]
    calc
      (p * r) * (a k₁ * a k₂) = (p * a k₁) * (r * a k₂) := by ac_rfl
      _ = (q * a k₁') * (s * a k₂') := congrArg₂ (· * ·) h₁ h₂
      _ = (q * s) * (a k₁' * a k₂') := by ac_rfl

private abbrev quotObj {P K : CommMonCat.{w}} (a : K ⟶ P) : CommMonCat.{w} :=
  CommMonCat.of (quotCon a).Quotient

private def quotMk {P K : CommMonCat.{w}} (a : K ⟶ P) : P ⟶ quotObj a :=
  CommMonCat.ofHom (quotCon a).mk'

private theorem quotMk_image_eq_one {P K : CommMonCat.{w}} (a : K ⟶ P) (k : K) :
    quotMk a (a k) = 1 := by
  apply (quotCon a).eq.mpr
  exact ⟨1, k, by simp⟩

private theorem integralRightCancel {P : CommMonCat.{w}}
    (hP : IsIntegralMonoid P) : IsRightCancelMul P where
  mul_right_cancel c := by
    intro x y h
    apply hP
    have hm := congrArg (Algebra.GrothendieckGroup.of (M := P)) h
    exact mul_right_cancel (by simpa only [map_mul] using hm)

private theorem quotRightCancel {P K : CommMonCat.{w}} (a : K ⟶ P)
    (hP : IsIntegralMonoid P) : IsRightCancelMul (quotObj a) where
  mul_right_cancel c := by
    intro x y h
    induction c using Con.induction_on with | H c => ?_
    induction x using Con.induction_on with | H x => ?_
    induction y using Con.induction_on with | H y => ?_
    obtain ⟨k, k', hk⟩ := (quotCon a).eq.mp h
    apply (quotCon a).eq.mpr
    refine ⟨k, k', ?_⟩
    let : IsRightCancelMul P := integralRightCancel hP
    apply mul_right_cancel (b := c)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hk

private theorem quotFine {P K : CommMonCat.{w}} (a : K ⟶ P)
    (hP : IsFineMonoid P) : IsFineMonoid (quotObj a) := by
  let : IsRightCancelMul (quotObj a) := quotRightCancel a hP.1
  let : IsLeftCancelMul (quotObj a) := ⟨fun c x y h =>
    mul_right_cancel (b := c) (by simpa only [mul_comm] using h)⟩
  let : IsCancelMul (quotObj a) := ⟨⟩
  let : IsMulFG P := hP.2
  exact ⟨Algebra.GrothendieckGroup.of_injective,
    IsMulFG.of_surjective (quotCon a).mk' (Con.mk'_surjective (c := quotCon a))⟩

private theorem quotSharp {P O K : CommMonCat.{w}} (f : P ⟶ O) (a : K ⟶ P)
    (himage : ∀ p : P, (∃ k : K, a k = p) ↔ IsUnit (f p)) :
    IsSharpMonoid (quotObj a) := by
  intro p hp
  obtain ⟨q, hq⟩ := hp.exists_right_inv
  induction p using Con.induction_on with | H p => ?_
  induction q using Con.induction_on with | H q => ?_
  obtain ⟨k, k', hk⟩ := (quotCon a).eq.mp hq
  have hu := (himage (a k')).mp ⟨k', rfl⟩
  have he : f (p * q * a k) = f (a k') := congrArg f (by simpa using hk)
  rw [← he, map_mul, map_mul] at hu
  have hp' : IsUnit (f p) := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hu).1).1
  obtain ⟨k, rfl⟩ := (himage p).mpr hp'
  exact quotMk_image_eq_one a k

private theorem get_chart_data
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fine : HasFineCharts J L)
    (p : J.Point.{max u v}) :
    ∃ (V : C) (_xV : p.fiber.obj V) (P : CommMonCat.{max u v}),
      IsFineMonoid P ∧ Nonempty (Chart J L V P) := by
  obtain ⟨e⟩ := IsCofiltered.nonempty (C := p.fiber.Elements)
  obtain ⟨I, V, f, hcov, hc⟩ := fine e.obj
  obtain ⟨Y, g, hg, y, _⟩ := p.jointly_surjective _ hcov e.val
  obtain ⟨W, h, k, ⟨i⟩, _⟩ := hg
  obtain ⟨P, hp, chart⟩ := hc i
  exact ⟨V i, p.fiber.map h y, P, hp, chart⟩

private def quotDesc {P K R : CommMonCat.{w}} {a : K ⟶ P} (i : P ⟶ R)
    (h : ∀ k : K, i (a k) = 1) : quotObj a ⟶ R :=
  CommMonCat.ofHom ((quotCon a).lift i.hom (by
    rintro p q ⟨k, k', hk⟩
    change i p = i q
    have he := congrArg i hk
    simpa only [map_mul, h, mul_one] using he))

private theorem quotDesc_mk {P K R : CommMonCat.{w}} {a : K ⟶ P} (i : P ⟶ R)
    (h : ∀ k : K, i (a k) = 1) (p : P) :
    quotDesc i h (quotMk a p) = i p := rfl

private def quotientIso {P K T Q : CommMonCat.{w}}
    {a : K ⟶ P} {b : K ⟶ T} {i : P ⟶ Q} {j : T ⟶ Q}
    (ht : IsTerminal T) (h : IsPushout a b i j) : quotObj a ≅ Q := by
  let : Unique T := Types.isTerminalEquivUnique _ (ht.isTerminalObj (forget CommMonCat))
  have hb (k : K) : b k = 1 := Subsingleton.elim _ _
  have hkill (k : K) : i (a k) = 1 := by
    have he := ConcreteCategory.congr_hom h.w k
    simpa only [CommMonCat.comp_apply, hb, map_one] using he
  let q : T ⟶ quotObj a := CommMonCat.ofHom (1 : T →* quotObj a)
  have hw : a ≫ quotMk a = b ≫ q := by
    ext k
    exact quotMk_image_eq_one a k
  refine ⟨quotDesc i hkill, h.desc (quotMk a) q hw, ?_, ?_⟩
  · ext x
    change (h.desc (quotMk a) q hw) (i x) = quotMk a x
    exact ConcreteCategory.congr_hom (h.inl_desc (quotMk a) q hw) x
  · apply h.hom_ext
    · ext p
      change quotDesc i hkill ((h.desc (quotMk a) q hw) (i p)) = i p
      rw [← CommMonCat.comp_apply i (h.desc (quotMk a) q hw), h.inl_desc]
      exact quotDesc_mk i hkill p
    · ext t
      have ht' : t = 1 := Subsingleton.elim _ _
      subst t
      simp

private theorem isoFine {P Q : CommMonCat.{w}} (hP : IsFineMonoid P)
    (e : P ≅ Q) : IsFineMonoid Q := by
  let : IsRightCancelMul P := integralRightCancel hP.1
  let : IsRightCancelMul Q := ⟨fun c x y h => by
    apply (ConcreteCategory.bijective_of_isIso e.inv).1
    have he := congrArg e.inv h
    exact mul_right_cancel (by simpa only [map_mul] using he)⟩
  let : IsLeftCancelMul Q := ⟨fun c x y h =>
    mul_right_cancel (b := c) (by simpa only [mul_comm] using h)⟩
  let : IsCancelMul Q := ⟨⟩
  let : IsMulFG P := hP.2
  exact ⟨Algebra.GrothendieckGroup.of_injective,
    IsMulFG.of_surjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2⟩

private theorem isoSharp {P Q : CommMonCat.{w}} (hP : IsSharpMonoid P)
    (e : P ≅ Q) : IsSharpMonoid Q := by
  intro q hq
  have h := hP (e.inv q) (hq.map e.inv.hom)
  have he := congrArg e.hom h
  simpa using he

private theorem fiberUnitImage {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (O : RingSheaf J) (p : J.Point.{max u v})
    (r : (p.sheafFiber (A := CommMonCat)).obj (ringMonoids J O)) :
    (∃ t : (p.sheafFiber (A := CommMonCat)).obj (units J O),
      p.sheafFiber.map (unitInclusion J O) t = r) ↔
      IsUnit r := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨X, x, z, rfl⟩ := p.toPresheafFiber_jointly_surjective t
    change IsUnit (p.presheafFiber.map (unitInclusion J O).hom
      (p.toPresheafFiber X x (units J O).obj z))
    rw [p.toPresheafFiber_naturality_apply]
    exact z.isUnit.map (p.toPresheafFiber X x (ringMonoids J O).obj).hom
  · intro hr
    obtain ⟨s, hs⟩ := hr.exists_right_inv
    obtain ⟨X, x, a, b, ha, hb⟩ :=
      p.toPresheafFiber_jointly_surjective₂ (P := (ringMonoids J O).obj) r s
    have he : p.toPresheafFiber X x (ringMonoids J O).obj (a * b) =
        p.toPresheafFiber X x (ringMonoids J O).obj 1 := by
      rw [map_mul, ha, hb, map_one]
      exact hs
    obtain ⟨Y, f, y, hy, hab⟩ :=
      (p.toPresheafFiber_eq_iff' (P := (ringMonoids J O).obj) X x (a * b) 1).mp he
    let a' := (ringMonoids J O).obj.map f.op a
    let b' := (ringMonoids J O).obj.map f.op b
    have he' : a' * b' = 1 := by simpa only [map_mul, map_one] using hab
    let z : (units J O).obj.obj (op Y) :=
      ⟨a', b', he', by simpa only [mul_comm] using he'⟩
    refine ⟨p.toPresheafFiber Y y (units J O).obj z, ?_⟩
    change p.presheafFiber.map (unitInclusion J O).hom
      (p.toPresheafFiber Y y (units J O).obj z) = r
    rw [p.toPresheafFiber_naturality_apply (unitInclusion J O).hom]
    change p.toPresheafFiber Y y (ringMonoids J O).obj
      ((ringMonoids J O).obj.map f.op a) = r
    rw [p.toPresheafFiber_w_apply, hy]
    exact ha

private def overFiberNatIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (p : J.Point.{max u v}) {V : C}
    (xV : p.fiber.obj V) :
    J.overPullback CommMonCat V ⋙ (p.over xV).sheafFiber ≅ p.sheafFiber :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf J CommMonCat ⋙
      (Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π p.fiber).op)
    (Functor.Final.colimIso (Gover J p xV).op)

/-- Local fine charts give fine sharp characteristic monoids at site points. -/
public theorem fine_characteristic
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fine : HasFineCharts J L)
    (p : J.Point.{max u v}) :
    IsFineMonoid (characteristicAt J L p) ∧ IsSharpMonoid (characteristicAt J L p) := by
  obtain ⟨V, xV, P, hP, ⟨chart⟩⟩ := get_chart_data J O L fine p
  let R := J.overPullback CommMonCat V
  let F := (p.over xV).sheafFiber (A := CommMonCat)
  let H := R ⋙ F
  let : PreservesFiniteLimits H :=
    preservesFiniteLimits_of_natIso (overFiberNatIso J p xV).symm
  let : PreservesFiniteColimits H :=
    preservesFiniteColimits_of_natIso (overFiberNatIso J p xV).symm
  let a₀ := pullback.fst (chart.map ≫ R.map (alpha J L)) (R.map (unitInclusion J O))
  let a := F.map a₀
  let f := F.map (chart.map ≫ R.map (alpha J L))
  have hpull := ((IsPullback.of_hasPullback
    (chart.map ≫ R.map (alpha J L)) (R.map (unitInclusion J O))).map F).map
      (forget CommMonCat)
  have himage (t : F.obj ((constantSheaf (J.over V) CommMonCat).obj P)) :
      (∃ k, a k = t) ↔ IsUnit (f t) := by
    change t ∈ Set.range ((forget CommMonCat).map a) ↔ IsUnit (f t)
    rw [Types.range_fst_of_isPullback hpull]
    exact fiberUnitImage (J.over V) ((J.overPullback CommRingCat V).obj O)
      (p.over xV) (f t)
  have hchart := chart.pushout.map F
  have hchar := (IsPushout.of_hasPushout (unitMap J L)
    (terminal.from (units J O))).map H
  have hpaste := hchart.paste_vert hchar
  let e := quotientIso (terminalIsTerminal.isTerminalObj H) hpaste
  have hsource : IsFineMonoid (F.obj ((constantSheaf (J.over V) CommMonCat).obj P)) :=
    isoFine hP (sheafConstFiberIso (J.over V) (p.over xV) P).symm
  have hq := quotFine a hsource
  have hs := quotSharp f a himage
  let e' := e ≪≫ overFiberIso J p xV (characteristic J L)
  exact ⟨isoFine hq e', isoSharp hs e'⟩

end WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted
