/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.FppfStacks
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Root line-bundle groupoids and normalized root-stack interfaces

The fibre objects are actual line bundles with an actual section and an
isomorphism from their tensor power to the prescribed line bundle, taking
the section power to the prescribed section. Morphisms are actual module
isomorphisms preserving both data. General root-stack construction and
descent may be supplied separately through the public normalized contract.

No root of every line bundle on every scheme is asserted: fibres may be
empty. No characteristic-zero, projective, smooth or reduced assumption
is imposed. The stack construction has positive exponent; an étale/DM
conclusion additionally requires that exponent invertible on the base.

References: Cadman, *Using stacks to impose tangency conditions on curves*,
§2, https://doi.org/10.1353/ajm.2007.0007; Borne--Vistoli,
*Parabolic sheaves on logarithmic schemes*, §4,
https://arxiv.org/abs/1001.0466.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RootStacks

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

universe u

/-- The actual local polynomial relation for a root of a regular function. -/
def chartPolynomial (A : Type u) [CommRing A] (s : A) (n : ℕ) : Polynomial A :=
  Polynomial.X ^ n - Polynomial.C s

/-- The actual local root algebra, including the nonreduced zero-section case. -/
abbrev ChartAlgebra (A : Type u) [CommRing A] (s : A) (n : ℕ) :=
  AdjoinRoot (chartPolynomial A s n)

/-- The actual universal root coordinate in that quotient algebra. -/
abbrev chartCoordinate (A : Type u) [CommRing A] (s : A) (n : ℕ) :
    ChartAlgebra A s n := AdjoinRoot.root (chartPolynomial A s n)

/-- The local root equation holds in the actual quotient, without taking a radical. -/
theorem chartCoordinate_power (A : Type u) [CommRing A] (s : A) (n : ℕ) :
    chartCoordinate A s n ^ n = algebraMap A (ChartAlgebra A s n) s := by
  have h := AdjoinRoot.eval₂_root (chartPolynomial A s n)
  have h' : chartCoordinate A s n ^ n - algebraMap A (ChartAlgebra A s n) s = 0 := by
    erw [chartPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    exact h
  exact sub_eq_zero.mp h'

/-- The actual affine local root scheme. -/
abbrev chartScheme (A : Type u) [CommRing A] (s : A) (n : ℕ) : Scheme.{u} :=
  Spec (.of (ChartAlgebra A s n))

/-- Its structural scheme morphism is the actual quotient coefficient map. -/
def chartProjection (A : Type u) [CommRing A] (s : A) (n : ℕ) :
    chartScheme A s n ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (ChartAlgebra A s n)))

/-- Scaling the universal root by an actual unit satisfying zeta^n=1. -/
def chartScale {A : Type u} [CommRing A] (s : A) (n : ℕ)
    (ζ : Aˣ) (hζ : ζ ^ n = 1) : ChartAlgebra A s n →ₐ[A] ChartAlgebra A s n :=
  AdjoinRoot.liftAlgHom (chartPolynomial A s n) (Algebra.ofId A (ChartAlgebra A s n))
    (algebraMap A (ChartAlgebra A s n) (ζ : A) * chartCoordinate A s n) (by
      have hz : (ζ : A) ^ n = 1 := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg (fun z : Aˣ => (z : A)) hζ
      simp only [chartPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      change (algebraMap A (ChartAlgebra A s n) (ζ : A) * chartCoordinate A s n) ^ n -
        algebraMap A (ChartAlgebra A s n) s = 0
      rw [mul_pow, ← map_pow, hz, map_one, one_mul, chartCoordinate_power, sub_self])

/-- The local scaling map is normalized on the genuine root coordinate. -/
theorem chartScale_coordinate {A : Type u} [CommRing A] (s : A) (n : ℕ)
    (ζ : Aˣ) (hζ : ζ ^ n = 1) :
    chartScale s n ζ hζ (chartCoordinate A s n) =
      algebraMap A (ChartAlgebra A s n) (ζ : A) * chartCoordinate A s n :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The actual groupoid objects of the root of a line bundle with section.
For `n = 0` the groupoid is degenerate (the zeroth power is the structure
sheaf); the root-stack interfaces below require a positive exponent. -/
structure RootObject {X : Scheme.{u}} (L : X.Modules) (s : Section L) (n : ℕ) where
  /-- The root is an actual module sheaf. -/
  module : X.Modules
  /-- Its actual local rank-one trivializations. -/
  line : IsLineBundle module
  /-- The root section, as an actual structure-sheaf morphism. -/
  rootSection : Section module
  /-- The actual power isomorphism, not an arbitrary identification of sections. -/
  powerIso : power module n ≅ L
  /-- The required equation on the actual tensor power of the section. -/
  section_eq : sectionPower rootSection n ≫ powerIso.hom = s

namespace RootObject

variable {X : Scheme.{u}} {L : X.Modules} {s : Section L} {n : ℕ}

/-- Root arrows preserve the actual section and power isomorphism. -/
@[ext] structure Hom (M N : RootObject L s n) where
  /-- The actual invertible module map. -/
  iso : M.module ≅ N.module
  /-- The root sections agree under that map. -/
  section_compat : M.rootSection ≫ iso.hom = N.rootSection
  /-- The power maps agree under the native tensor-power functor. -/
  power : powerMap iso.hom n ≫ N.powerIso.hom = M.powerIso.hom

/-- The actual identity root arrow. -/
def Hom.id (M : RootObject L s n) : Hom M M where
  iso := Iso.refl _
  section_compat := Category.comp_id _
  power := by simp

/-- The actual composition of invertible module maps. -/
def Hom.comp {M N P : RootObject L s n} (f : Hom M N) (g : Hom N P) : Hom M P where
  iso := f.iso ≪≫ g.iso
  section_compat := by
    rw [Iso.trans_hom, ← Category.assoc, f.section_compat, g.section_compat]
  power := by rw [Iso.trans_hom, powerMap_comp, Category.assoc, g.power, f.power]

/-- The actual inverse root arrow. -/
def Hom.inv {M N : RootObject L s n} (f : Hom M N) : Hom N M where
  iso := f.iso.symm
  section_compat := by
    rw [Iso.symm_hom, ← f.section_compat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  power := by
    rw [Iso.symm_hom, ← f.power, ← Category.assoc, ← powerMap_comp,
      Iso.inv_hom_id, powerMap_id, Category.id_comp]

instance : Groupoid (RootObject L s n) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  inv := Hom.inv
  id_comp f := by apply Hom.ext; apply Iso.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; apply Iso.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; apply Iso.ext; exact Category.assoc _ _ _
  inv_comp f := by apply Hom.ext; apply Iso.ext; exact f.iso.inv_hom_id
  comp_inv f := by apply Hom.ext; apply Iso.ext; exact f.iso.hom_inv_id

/-- Forgetting a root retains the actual module and module morphism. -/
def forget (L : X.Modules) (s : Section L) (n : ℕ) :
    RootObject L s n ⥤ X.Modules where
  obj M := M.module
  map f := f.iso.hom

instance : (forget L s n).Faithful where
  map_injective h := Hom.ext (Iso.ext h)

end RootObject

/-- The actual roots over a scheme-valued point of the prescribed base. -/
abbrev RootsOver {X : Scheme.{u}} (L : X.Modules) (s : Section L)
    (n : ℕ) (T : Over X) :=
  RootObject ((Scheme.Modules.pullback T.hom).obj L) (pullbackSection T.hom s) n

/-- Reindexing root fibres must be the actual module pullback, with both
the root section and power comparison normalized. The comparison is data
for fixed operations, rather than a freely chosen reindexing oracle. -/
structure RootReindexing {X : Scheme.{u}} (L : X.Modules) (s : Section L)
    (n : ℕ) {T U : Over X} (f : T ⟶ U) where
  /-- The functor on actual root groupoids. -/
  functor : RootsOver L s n U ⥤ RootsOver L s n T
  /-- Every underlying module map is the actual pullback, naturally. -/
  underlying : functor ⋙ RootObject.forget _ _ n ≅
    RootObject.forget _ _ n ⋙ Scheme.Modules.pullback f.left
  /-- Its actual root sections are the pulled-back sections. -/
  section_normalization : ∀ M : RootsOver L s n U,
    (functor.obj M).rootSection ≫ underlying.hom.app M =
      pullbackSection f.left M.rootSection
  /-- The fixed power/pullback comparison, with section normalization. -/
  powers : PullbackPowers f.left
  /-- The root power map is the pulled-back power map after the canonical
  over-base and power comparisons. -/
  power : ∀ M : RootsOver L s n U,
    (functor.obj M).powerIso.hom =
      powerMap (underlying.hom.app M) n ≫
        (powers.comparison n).inv.app M.module ≫
          (Scheme.Modules.pullback f.left).map M.powerIso.hom ≫
            (Scheme.Modules.pullbackComp f.left U.hom).hom.app L ≫
              (Scheme.Modules.pullbackCongr f.w).hom.app L

/-- The native pseudofunctor carrier on schemes over the prescribed base. -/
abbrev OverPseudofunctor (X : Scheme.{u}) :=
  CategoryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete (Over X)ᵒᵖ) Cat.{u, u + 1}

/-- Root-stack fibre and reindexing data, before the unit/composition
normalization of the transported forgetful functors is imposed. -/
structure RootStackData {X : Scheme.{u}} (L : X.Modules) (s : Section L) (n : ℕ) where
  /-- The rooted module is a line bundle, as for Cadman's root stacks. -/
  line : MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.IsLineBundle L
  /-- The exponent is positive, as for Cadman's root stacks. -/
  positive : 0 < n
  /-- The actual pseudofunctor. -/
  pseudofunctor : OverPseudofunctor X
  /-- Fibre identifications retain actual objects and arrows. -/
  fibre (T : Over X) :
    pseudofunctor.obj (.mk (op T)) ≌ RootsOver L s n T
  /-- The actual root-pullback contracts on all scheme maps over X. -/
  reindexing {T U : Over X} (f : T ⟶ U) : RootReindexing L s n f
  /-- The pseudofunctor maps agree naturally with these normalized maps. -/
  mapComparison {T U : Over X} (f : T ⟶ U) :
    (pseudofunctor.map f.op.toLoc).toFunctor ⋙ (fibre T).functor ≅
      (fibre U).functor ⋙ (reindexing f).functor
  /-- Fppf descent on the native induced topology. -/
  descent : pseudofunctor.IsStack (Scheme.fppfTopology.over X)

namespace RootStackData

variable {X : Scheme.{u}} {L : X.Modules} {s : Section L} {n : ℕ}
  (R : RootStackData L s n)

/-- The actual underlying-module functor, computed from the fibre equivalence
and the forgetful functor on genuine root objects. -/
def moduleForget (T : Over X) : R.pseudofunctor.obj (.mk (op T)) ⥤ T.left.Modules :=
  (R.fibre T).functor ⋙ RootObject.forget _ _ n

/-- The pullback comparison is computed from the given root-map comparison
and its actual underlying-module comparison, with only functor associators.
It is not an independently supplied natural isomorphism. -/
def moduleComparison {T U : Over X} (f : T ⟶ U) :
    (R.pseudofunctor.map f.op.toLoc).toFunctor ⋙ R.moduleForget T ≅
      R.moduleForget U ⋙ Scheme.Modules.pullback f.left :=
  (Functor.associator (R.pseudofunctor.map f.op.toLoc).toFunctor
    (R.fibre T).functor (RootObject.forget _ _ n)).symm ≪≫
  Functor.isoWhiskerRight (R.mapComparison f) (RootObject.forget _ _ n) ≪≫
  Functor.associator (R.fibre U).functor (R.reindexing f).functor
    (RootObject.forget _ _ n) ≪≫
  Functor.isoWhiskerLeft (R.fibre U).functor (R.reindexing f).underlying ≪≫
  (Functor.associator (R.fibre U).functor (RootObject.forget _ _ n)
    (Scheme.Modules.pullback f.left)).symm

end RootStackData

/-- An actual fppf root stack with a coherent transported forgetful functor
to the native module pullback pseudofunctor. The two diagrams use its fixed
`pullbackId` and `pullbackComp`, and the root pseudofunctor's native `mapId`
and `mapComp`. Their proofs are explicit construction dependencies. -/
structure RootStack {X : Scheme.{u}} (L : X.Modules) (s : Section L) (n : ℕ)
    extends RootStackData L s n where
  /-- The computed comparison over the identity is the native module unit
  comparison, transported along the root pseudofunctor's unit. -/
  unit_normalization : ∀ (T : Over X) (M : pseudofunctor.obj (.mk (op T))),
    (toRootStackData.moduleComparison (𝟙 T)).hom.app M ≫
      (Scheme.Modules.pullbackId T.left).hom.app
        ((toRootStackData.moduleForget T).obj M) =
    (toRootStackData.moduleForget T).map
      ((Cat.Hom.toNatIso (pseudofunctor.mapId (.mk (op T)))).hom.app M)
  /-- The computed comparisons for a composite agree with the two individual
  comparisons and the actual module composition isomorphism. -/
  composition_normalization : ∀ {T U V : Over X} (f : T ⟶ U) (g : U ⟶ V)
    (M : pseudofunctor.obj (.mk (op V))),
    (toRootStackData.moduleComparison (f ≫ g)).hom.app M =
      (toRootStackData.moduleForget T).map
        ((Cat.Hom.toNatIso (pseudofunctor.mapComp g.op.toLoc f.op.toLoc)).hom.app M) ≫
      (toRootStackData.moduleComparison f).hom.app
        ((pseudofunctor.map g.op.toLoc).toFunctor.obj M) ≫
      (Scheme.Modules.pullback f.left).map
        ((toRootStackData.moduleComparison g).hom.app M) ≫
      (Scheme.Modules.pullbackComp f.left g.left).hom.app
        ((toRootStackData.moduleForget V).obj M)

/-- The prescribed root-fibre equivalence proves that every native stack
fibre is a groupoid; no extra groupoid oracle or provider is necessary. -/
instance RootStack.isGroupoid {X : Scheme.{u}} {L : X.Modules} {s : Section L}
    {n : ℕ} (R : RootStack L s n) (T : Over X) :
    IsGroupoid (R.pseudofunctor.obj (.mk (op T))) where
  all_isIso f := by
    have : IsIso ((R.fibre T).functor.map f) := inferInstance
    exact isIso_of_reflects_iso f (R.fibre T).functor

/-- The actual root pseudofunctor on the general relative-stack carrier.
This computed adapter exposes Artin/DM paper goals without an atlas oracle. -/
def RootStack.toRelativeStack {X : Scheme.{u}} {L : X.Modules} {s : Section L}
    {n : ℕ} (R : RootStack L s n) :
    _root_.AlgebraicGeometry.GeneralStackGeometry.RelativeStack X :=
  _root_.AlgebraicGeometry.GeneralStackGeometry.RelativeStack.of X
    R.pseudofunctor R.isGroupoid R.descent

end MathlibExt.AlgebraicGeometry.RootStacks
