/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotients
public import MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels
public import MathlibExt.AlgebraicGeometry.GeneralModuleTotalSpaces
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry

/-!
# Actual bundle Thom objects, zero pullback and relative finite cycles

The total space is the section-representing source construction of the
given locally free module (Spec Sym of its dual). Its zero section is the
actual map represented by zero. Thom is the pointed cofiber of the
complement of that same zero section. Euler is its native cohomology
pullback, and relative cycle generators are actual finite correspondences
whose two base projections agree as whole scheme morphisms.

Sources: Voevodsky arXiv:math/0107109v1, Sections 4--5, pp. 12--17;
Stacks Project, VectorBundleOfModule, source revision
c496df0d9beea9deaeabcea8492605f9a0a2313b. The imported total-space source
retains its attribution and the section/dual convention.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicBundleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels PointedMotivicQuotients
open GeneralModuleTotalSpaces
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- Actual smooth bundle geometry with the complement of the represented
zero section, for every rank including zero. -/
structure BundleGeometry (X : SmoothScheme k) (M : X.scheme.left.Modules)
    (rank : ℕ) where
  locallyFree : MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry.IsBundle M rank
  total : TotalSpace X.scheme.left M
  smoothTotal : SmoothScheme k
  totalIso : smoothTotal.scheme.left ≅ total.total
  base_eq : smoothTotal.scheme.hom =
    totalIso.hom ≫ total.projection ≫ X.scheme.hom
  [closedZero : IsClosedImmersion (total.zero ≫ totalIso.inv)]
  complement : SmoothScheme k
  complementInclusion : complement ⟶ smoothTotal
  [openComplement : IsOpenImmersion complementInclusion.left]
  complement_eq : Set.range complementInclusion.left =
    (Set.range (total.zero ≫ totalIso.inv))ᶜ

attribute [instance] BundleGeometry.closedZero BundleGeometry.openComplement

namespace BundleGeometry

variable {X : SmoothScheme k} {M : X.scheme.left.Modules} {rank : ℕ}
  (G : BundleGeometry X M rank)

/-- The native bundle projection, with its actual field structure map. -/
def projection : G.smoothTotal ⟶ X :=
  Over.homMk (G.totalIso.hom ≫ G.total.projection) (by
    simpa only [Category.assoc] using G.base_eq.symm)

/-- The source-normalized zero section represented by the zero module section. -/
def zero : X ⟶ G.smoothTotal :=
  Over.homMk (G.total.zero ≫ G.totalIso.inv) (by
    rw [G.base_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, G.total.zero_projection, Category.id_comp])

/-- The pointed Thom object is the actual total space modulo its open
complement of the zero section. -/
def thom : PointedSpaces (k := k) :=
  cofiber (representedMap G.complementInclusion)

/-- The actual zero-section map into the native pointed Thom quotient. -/
def zeroThom : representedPointed X ⟶ G.thom :=
  representedMap G.zero ≫ cofiberQuotient (representedMap G.complementInclusion)

/-- A generator is relative to X exactly when its two actual scheme base
maps agree, not merely when its support has the expected dimension. -/
def IsRelativeGenerator (z : Generator X G.smoothTotal) : Prop :=
  z.presentation.inclusion ≫
    pullback.snd X.scheme.hom G.smoothTotal.scheme.hom ≫ G.projection.left =
  z.presentation.inclusion ≫ pullback.fst X.scheme.hom G.smoothTotal.scheme.hom

/-- Actual integral finite relative bundle-cycle generators. -/
abbrev RelativeGenerator := {z : Generator X G.smoothTotal // G.IsRelativeGenerator z}

/-- Integral relative finite cycles on this same actual bundle total space. -/
abbrev RelativeCycles := G.RelativeGenerator →₀ ℤ

/-- The native forgetful map is the free cycle map on these actual supports. -/
def forgetRelativeCycles (z : G.RelativeCycles) : Cycles X G.smoothTotal :=
  Finsupp.mapDomain Subtype.val z

end BundleGeometry

/-- The actual total-space map of a module morphism, using the target's
representing universal property and the pulled-back source universal section. -/
def totalMap {X : Scheme.{0}} {M N : X.Modules}
    (V : TotalSpace X M) (W : TotalSpace X N) (a : M ⟶ N) : V.total ⟶ W.total :=
  W.lift V.projection
    ((((Scheme.Modules.pullback V.projection).map a).val.app (op ⊤)).hom
      V.universalSection)

/-- This total-space map is over the original base as a whole scheme morphism. -/
theorem totalMap_over {X : Scheme.{0}} {M N : X.Modules}
    (V : TotalSpace X M) (W : TotalSpace X N) (a : M ⟶ N) :
    totalMap V W a ≫ W.projection = V.projection := W.lift_over _ _

/-- The actual affine Thom sphere A^q/(A^q minus zero), independently of
the reduced-torus definition of the Tate coefficient complex. -/
def affineThomSphere {P : SmoothProductSystem k} (A : StandardSchemes P) (q : ℕ) :
    PointedSpaces (k := k) := cofiber (representedMap (A.complementInclusion q))

variable {D : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D G₀] [CorrespondenceAdditivity D G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G₀ P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G₀} {S : TransferSheafificationModel D G₀}
  {T : CycleComplexSystem (D := D) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (F : ReducedFreeNisSystem k)

/-- The Euler operation is precisely the actual zero pullback of a
specified Thom class on this actual bundle geometry. -/
def eulerClass {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) (V : ModuleCat.{1} ℤ)
    (t : ReducedCohomology B F G.thom (2 * (d : ℤ)) (d : ℤ) V) :
    ReducedCohomology B F (representedPointed X) (2 * (d : ℤ)) (d : ℤ) V :=
  ReducedMotivicCohomologyModels.pullback B F G.zeroThom (2 * (d : ℤ)) (d : ℤ) V t

end MathlibExt.AlgebraicGeometry.MotivicBundleModels
