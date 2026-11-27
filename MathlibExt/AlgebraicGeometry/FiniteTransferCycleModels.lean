/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import MathlibExt.AlgebraicGeometry.NisnevichResidueDegreeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Finite equidimensional transfer cycles on actual smooth schemes

Generators are closed supports with an integral closed-scheme presentation,
finite and surjective over a connected component of the smooth source.
Only the support and propositions are retained by the generator, so choosing
an isomorphic presentation does not create another cycle generator.

The composition kernel uses the actual pulled-back closed schemes. Its
generic coefficients are alternating native Tor lengths, followed by the
actual residue-degree pushforward. All geometry and finiteness construction
outputs are separate from category laws in the corresponding Wanted module.

References: Voevodsky, arXiv:math/0107109v1, §2 pp.3--4; Suslin--Voevodsky,
Relative cycles and Chow sheaves, §2; Fulton, Intersection Theory, §20.4.
Integral support/length vocabulary uses the public-source dictionaries in
IntegerSchemeChow and StackCycleGeometry; native Tor is Mathlib's functor.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.IntegerSchemeChow
open TopologicalSpace

variable {k : Type} [Field k]

/-- Smooth separated finite-type schemes over the actual field spectrum. -/
structure SmoothScheme (k : Type) [Field k] extends FieldScheme k where
  [smooth : Smooth scheme.hom]
  [separated : IsSeparated scheme.hom]

attribute [instance] SmoothScheme.smooth SmoothScheme.separated

instance : Category.{0} (SmoothScheme k) where
  Hom X Y := X.scheme ⟶ Y.scheme
  id X := 𝟙 X.scheme
  comp f g := f ≫ g
  id_comp f := by simp
  comp_id f := by simp
  assoc f g h := by simp [Category.assoc]

def schemeFunctor : SmoothScheme k ⥤ Scheme.{0} where
  obj X := X.scheme.left
  map f := f.left

def productScheme (U X : SmoothScheme k) : Scheme.{0} :=
  pullback U.scheme.hom X.scheme.hom

/-- A presentation of one actual reduced integral closed support. -/
structure SupportPresentation (U X : SmoothScheme k) (s : Closeds (productScheme U X)) where
  scheme : Scheme.{0}
  [integral : IsIntegral scheme]
  [noetherian : IsNoetherian scheme]
  inclusion : scheme ⟶ productScheme U X
  [closed : IsClosedImmersion inclusion]
  [finite : IsFinite (inclusion ≫ pullback.fst U.scheme.hom X.scheme.hom)]
  support_eq : Set.range inclusion = (s : Set (productScheme U X))
  component : ∃ u : U.scheme.left,
    Set.range (inclusion ≫ pullback.fst U.scheme.hom X.scheme.hom) = connectedComponent u

attribute [instance] SupportPresentation.integral SupportPresentation.noetherian
  SupportPresentation.closed SupportPresentation.finite

/-- The basis is a support, rather than a name for a selected scheme presentation. -/
structure Generator (U X : SmoothScheme k) where
  support : Closeds (productScheme U X)
  represented : Nonempty (SupportPresentation U X support)

def Generator.presentation {U X : SmoothScheme k} (g : Generator U X) : SupportPresentation U X g.support :=
  Classical.choice g.represented

/-- Integral finite-transfer cycles, with no rational-equivalence quotient. -/
abbrev Cycles (U X : SmoothScheme k) := Generator U X →₀ ℤ

def generatorCycle {U X : SmoothScheme k} (g : Generator U X) : Cycles U X :=
  Finsupp.single g 1

/-- The native module of a ring with its scalar action fixed by the displayed ring homomorphism. -/
def ringModule {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : ModuleCat.{0} R := by
  letI := Module.compHom S f
  exact ModuleCat.of R S

def intersectionScheme {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) : Scheme.{0} := pullback i j

def intersectionPoint {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) : A :=
  i (pullback.fst i j t)

theorem intersectionPointEq {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) :
    intersectionPoint i j t = j (pullback.snd i j t) := by
  exact congrArg (fun f : pullback i j ⟶ A => f t) (pullback.condition (f := i) (g := j))

abbrev intersectionRing {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) :=
  A.presheaf.stalk (intersectionPoint i j t)

def intersectionLeft {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) :
    ModuleCat.{0} (intersectionRing i j t) :=
  ringModule (i.stalkMap (pullback.fst i j t)).hom

def intersectionRight {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) :
    ModuleCat.{0} (intersectionRing i j t) :=
  ringModule ((eqToHom (congrArg A.presheaf.stalk (intersectionPointEq i j t))) ≫
    j.stalkMap (pullback.snd i j t)).hom

/-- Actual local Tor, with both module actions supplied by native closed-immersion stalk maps. -/
def intersectionTor {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) (n : ℕ) :
    ModuleCat.{0} (intersectionRing i j t) :=
  ((Tor (ModuleCat.{0} (intersectionRing i j t)) n).obj (intersectionLeft i j t)).obj (intersectionRight i j t)

/-- The bounded local Euler characteristic includes finite-length and eventual-vanishing proofs. -/
structure LocalTorBounds {A Z W : Scheme.{0}} (i : Z ⟶ A) (j : W ⟶ A) (t : intersectionScheme i j) where
  bound : ℕ
  finite : ∀ n : ℕ, Module.length (intersectionRing i j t) (intersectionTor i j t n) ≠ ⊤
  vanishes : ∀ n : ℕ, bound ≤ n → IsZero (intersectionTor i j t n)

def LocalTorBounds.euler {A Z W : Scheme.{0}} {i : Z ⟶ A} {j : W ⟶ A} {t : intersectionScheme i j}
    (D : LocalTorBounds i j t) : ℤ :=
  ∑ n ∈ Finset.range D.bound,
    (-1 : ℤ) ^ n * ((Module.length (intersectionRing i j t) (intersectionTor i j t n)).toNat : ℤ)

def tripleScheme (U X Y : SmoothScheme k) : Scheme.{0} :=
  pullback (pullback.snd U.scheme.hom X.scheme.hom) (pullback.fst X.scheme.hom Y.scheme.hom)

def pulledLeft {U X Y : SmoothScheme k} (g : Generator U X) : Scheme.{0} :=
  pullback g.presentation.inclusion
    (pullback.fst (pullback.snd U.scheme.hom X.scheme.hom) (pullback.fst X.scheme.hom Y.scheme.hom))

def pulledRight {U X Y : SmoothScheme k} (h : Generator X Y) : Scheme.{0} :=
  pullback h.presentation.inclusion
    (pullback.snd (pullback.snd U.scheme.hom X.scheme.hom) (pullback.fst X.scheme.hom Y.scheme.hom))

def leftInclusion {U X Y : SmoothScheme k} (g : Generator U X) : pulledLeft (Y := Y) g ⟶ tripleScheme U X Y :=
  pullback.snd _ _

def rightInclusion {U X Y : SmoothScheme k} (h : Generator X Y) : pulledRight (U := U) h ⟶ tripleScheme U X Y :=
  pullback.snd _ _

abbrev compositionScheme {U X Y : SmoothScheme k} (g : Generator U X) (h : Generator X Y) :=
  intersectionScheme (leftInclusion (Y := Y) g) (rightInclusion (U := U) h)

/-- The projection to U×Y is fixed on both actual scheme-product coordinates. -/
structure CompositionProjection {U X Y : SmoothScheme k} (g : Generator U X) (h : Generator X Y) where
  map : compositionScheme g h ⟶ productScheme U Y
  fst_eq : map ≫ pullback.fst U.scheme.hom Y.scheme.hom =
    pullback.fst (leftInclusion g) (rightInclusion h) ≫ leftInclusion g ≫
      pullback.fst (pullback.snd U.scheme.hom X.scheme.hom) (pullback.fst X.scheme.hom Y.scheme.hom) ≫
      pullback.fst U.scheme.hom X.scheme.hom
  snd_eq : map ≫ pullback.snd U.scheme.hom Y.scheme.hom =
    pullback.snd (leftInclusion g) (rightInclusion h) ≫ rightInclusion h ≫
      pullback.snd (pullback.snd U.scheme.hom X.scheme.hom) (pullback.fst X.scheme.hom Y.scheme.hom) ≫
      pullback.snd X.scheme.hom Y.scheme.hom
  [finite : IsFinite map]

attribute [instance] CompositionProjection.finite

/-- A proper-intersection computation is fixed by local Tor and generic scheme-image supports. -/
structure CompositionGeometry {U X Y : SmoothScheme k} (g : Generator U X) (h : Generator X Y) where
  projection : CompositionProjection g h
  [noetherian : IsNoetherian (compositionScheme g h)]
  tor : ∀ z : irreducibleComponents (compositionScheme g h),
    LocalTorBounds (leftInclusion g) (rightInclusion h) z.2.1.genericPoint
  image : ∀ _z : irreducibleComponents (compositionScheme g h), Generator U Y
  image_eq : ∀ z : irreducibleComponents (compositionScheme g h),
    ((image z).support : Set (productScheme U Y)) = closure {projection.map z.2.1.genericPoint}

/-- The actual intersection/residue-degree cycle, with no chosen composition operation. -/
def CompositionGeometry.cycle {U X Y : SmoothScheme k} {g : Generator U X} {h : Generator X Y}
    (D : CompositionGeometry g h) : Cycles U Y := by
  letI := D.noetherian
  letI : Finite (irreducibleComponents (compositionScheme g h)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents (compositionScheme g h))
  exact ∑ z : irreducibleComponents (compositionScheme g h),
    ((D.tor z).euler * (D.projection.map.residueDegree z.2.1.genericPoint : ℤ)) • generatorCycle (D.image z)

/-- Geometry providers return only source-normalized intersection constructions. -/
structure CompositionSystem (k : Type) [Field k] where
  geometry : ∀ (U X Y : SmoothScheme k) (g : Generator U X) (h : Generator X Y), CompositionGeometry g h

/-- Bilinear extension of the fixed Tor/residue-degree kernel. -/
def composeCycles (D : CompositionSystem k) {U X Y : SmoothScheme k} (a : Cycles U X) (b : Cycles X Y) :
    Cycles U Y :=
  a.sum fun g n => b.sum fun h m => (n * m) • (D.geometry U X Y g h).cycle

/-- The actual graph into the product over the fixed field. -/
def graphMap {U X : SmoothScheme k} (f : U ⟶ X) : U.scheme.left ⟶ productScheme U X :=
  pullback.lift (𝟙 U.scheme.left) f.left (by simp)

/-- Each graph support is fixed by the image of an actual source generic point. -/
structure GraphGeometry {U X : SmoothScheme k} (f : U ⟶ X) where
  image : ∀ _z : irreducibleComponents U.scheme.left, Generator U X
  image_eq : ∀ z : irreducibleComponents U.scheme.left,
    ((image z).support : Set (productScheme U X)) = closure {graphMap f z.2.1.genericPoint}

def GraphGeometry.cycle {U X : SmoothScheme k} {f : U ⟶ X} (D : GraphGeometry f) : Cycles U X := by
  letI := U.noetherian
  letI : Finite (irreducibleComponents U.scheme.left) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents U.scheme.left)
  exact ∑ z : irreducibleComponents U.scheme.left, generatorCycle (D.image z)

structure GraphSystem (k : Type) [Field k] where
  geometry : ∀ (U X : SmoothScheme k) (f : U ⟶ X), GraphGeometry f

def graphCycle (G : GraphSystem k) {U X : SmoothScheme k} (f : U ⟶ X) : Cycles U X :=
  (G.geometry U X f).cycle

/-- These are laws of the fixed cycle operations, rather than freely chosen composition maps. -/
class CorrespondenceLaws (D : CompositionSystem k) (G : GraphSystem k) : Prop where
  left_unit : ∀ (U X : SmoothScheme k) (a : Cycles U X), composeCycles D (graphCycle G (𝟙 U)) a = a
  right_unit : ∀ (U X : SmoothScheme k) (a : Cycles U X), composeCycles D a (graphCycle G (𝟙 X)) = a
  assoc : ∀ (U X Y Z : SmoothScheme k) (a : Cycles U X) (b : Cycles X Y) (c : Cycles Y Z),
    composeCycles D (composeCycles D a b) c = composeCycles D a (composeCycles D b c)
  add_left : ∀ (U X Y : SmoothScheme k) (a a' : Cycles U X) (b : Cycles X Y),
    composeCycles D (a + a') b = composeCycles D a b + composeCycles D a' b
  add_right : ∀ (U X Y : SmoothScheme k) (a : Cycles U X) (b b' : Cycles X Y),
    composeCycles D a (b + b') = composeCycles D a b + composeCycles D a b'
  graph_comp : ∀ (U X Y : SmoothScheme k) (f : U ⟶ X) (g : X ⟶ Y),
    graphCycle G (f ≫ g) = composeCycles D (graphCycle G f) (graphCycle G g)

/-- Objects have the same actual schemes; the separate wrapper carries the finite-correspondence Hom. -/
structure CorrespondenceObject (D : CompositionSystem k) (G : GraphSystem k) where
  scheme : SmoothScheme k

instance (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] :
    Category.{0} (CorrespondenceObject D G) where
  Hom U X := Cycles U.scheme X.scheme
  id U := graphCycle G (𝟙 U.scheme)
  comp a b := composeCycles D a b
  id_comp {U X} a := CorrespondenceLaws.left_unit (D := D) (G := G) U.scheme X.scheme a
  comp_id {U X} a := CorrespondenceLaws.right_unit (D := D) (G := G) U.scheme X.scheme a
  assoc {U X Y Z} a b c :=
    CorrespondenceLaws.assoc (D := D) (G := G) U.scheme X.scheme Y.scheme Z.scheme a b c

/-- A preadditive structure on the category of finite correspondences `CorrespondenceObject D G`
over a field $k$ (for a composition system `D` and a graph system `G` satisfying
`CorrespondenceLaws`; its morphisms are integral finite-transfer cycles) in which the group
operations on morphisms are those of cycles, coefficientwise: the zero morphism has coefficient
$0$ at every generator, and the coefficient of $a + b$ (resp. $-a$) at each generator is the sum
of the coefficients of $a$ and $b$ (resp. the negative of that of $a$). -/
class CorrespondenceAdditivity (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] where
  preadditive : Preadditive (CorrespondenceObject D G)
  zero_coeff : letI := preadditive
    ∀ (U X : CorrespondenceObject D G) (z : Generator U.scheme X.scheme),
      (show Cycles U.scheme X.scheme from (0 : U ⟶ X)) z = 0
  add_coeff : letI := preadditive
    ∀ (U X : CorrespondenceObject D G) (a b : U ⟶ X) (z : Generator U.scheme X.scheme),
      (show Cycles U.scheme X.scheme from a + b) z =
        (show Cycles U.scheme X.scheme from a) z + (show Cycles U.scheme X.scheme from b) z
  neg_coeff : letI := preadditive
    ∀ (U X : CorrespondenceObject D G) (a : U ⟶ X) (z : Generator U.scheme X.scheme),
      (show Cycles U.scheme X.scheme from -a) z = -((show Cycles U.scheme X.scheme from a) z)

attribute [instance] CorrespondenceAdditivity.preadditive

def graphFunctor (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] :
    SmoothScheme k ⥤ CorrespondenceObject D G where
  obj U := ⟨U⟩
  map f := graphCycle G f
  map_id _U := rfl
  map_comp f g := CorrespondenceLaws.graph_comp (D := D) (G := G) _ _ _ f g

end MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
