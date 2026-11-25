/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Conductor

/-!
# Actual log-residue coefficients, different and conductor ideals

The local residue model uses the actual hypersurface quotient on affine
regular-function rings, pure Kähler top-form bases and the actual source
log-adjoint section. Its pulled section is computed by native unit,
pullbackComp, open restriction and evaluation maps.

A global residue comparison is fixed on that nonempty generic chart and
on every target Cartier generator. The different is computed from the
resulting actual Cartier divisor and chosen canonical form, not supplied
as a boundary function. Generic line/Cartier and normalization constructors
are completed source-integration inputs.

The affine conductor ideal is also computed, as the elements of the base
ring multiplying every normalization section into the actual base image.
It is a proved ideal. Conductor sheaf gluing and normalized branch
involutions are additional geometric contracts, not arbitrary involutions.

Sources: Hacon--McKernan--Xu, arXiv1412.1186v2, §§1/2.5;
Kollár, *Singularities of the Minimal Model Program*, adjunction/different.
Tau O(D) and native ring/module/normalization operations are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogResidueDifferent

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RationalFunctionModules
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable {k : Type} [Field k] {n : ℕ}

/-- A rationalization of the line bundle of Cartier data $C$ on a normal variety $V$ over $k$: a
morphism from the line bundle $L$ of $C$ to the sheaf $\mathcal{K}_V$ of rational functions sending,
on each chart $U_i$ of $C$, the chosen generator $s_i$ of $L$ over $U_i$ to $f_i^{-1}$, where
$f_i \in K(V)^\times$ is the local equation of $C$ on $U_i$ (sections of $\mathcal{K}_V$ over the
nonempty open $U_i$ being identified with the function field $K(V)$). -/
structure CartierRationalization {d : ℕ} {V : NormalVariety k d} (C : CartierLine V) where
  map : C.line.val ⟶ rationalFunctions V.X.left
  normalized : ∀ i,
    letI := C.nonempty i
    rationalFunctionsEquiv (C.opens i) (map.app (C.opens i) (C.sections i)) =
      (C.functions i : FunctionField V)⁻¹

/-- The actual pullback of a section on an ambient open to a divisor open. -/
def pullOpenSection {X S : Over (Spec (.of k))} (i : S ⟶ X)
    (M : X.left.Modules) (V : X.left.Opens) (U : S.left.Opens)
    (h : U ≤ i.left ⁻¹ᵁ V) (s : Γ(M,V)) :
    Γ((Scheme.Modules.pullback i.left).obj M,U) := by
  let XV : Over (Spec (.of k)) := Over.mk (V.ι ≫ X.hom)
  let SU : Over (Spec (.of k)) := Over.mk (U.ι ≫ S.hom)
  let a := i.left.resLE V U h
  let q := GenericSectionMaps.sectionHom XV ((Scheme.Modules.pullback V.ι).obj M)
    ((GenericSectionMaps.openSectionsIso X M V).inv s)
  let eq := Scheme.Hom.resLE_comp_ι i.left h
  let comparison :
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback V.ι).obj M) ⟶
        (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback i.left).obj M) :=
    (Scheme.Modules.pullbackComp a V.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr eq).hom.app M ≫
        (Scheme.Modules.pullbackComp U.ι i.left).inv.app M
  exact (GenericSectionMaps.openSectionsIso S ((Scheme.Modules.pullback i.left).obj M) U).hom
    (GenericSectionMaps.homSection SU (pullbackSection a q ≫ comparison))

/-- A genuine generic hypersurface residue chart, with both rational top-form bases fixed, for a
Cartier log-adjoint power `A = m (K_X + Δ)` with `m > 0` (`positive`, `adjointPower`).

The divisor side is the normalization of a coefficient-one boundary component: `i` is finite,
sends the generic point of `S` to the component `component`, and induces an isomorphism of its
residue field with the function field of `S` (`birational`). Since `S` is normal, this identifies
`S` with the normalization of the closure of `component`, where the different lives. -/
structure ResidueChart (P : LogPair k (n + 1)) (m : ℕ) (A : CartierLine P.variety)
    (S : NormalVariety k n) (C : CanonicalData S) (i : S.X ⟶ P.variety.X)
    (R : CartierRationalization A) where
  positive : 0 < m
  adjointPower : realCast A.divisor =
    (m : ℝ) • (realCast (canonicalDivisor P.canonical) + P.boundary)
  component : PrimePoint P.variety
  coefficientOne : P.boundary component = 1
  [finite : IsFinite i.left]
  generic : i.left (genericPoint S.X.left) = component.val
  birational : IsIso (i.left.residueFieldMap (genericPoint S.X.left))
  ambientOpen : P.variety.X.left.Opens
  divisorOpen : S.X.left.Opens
  [ambientNonempty : Nonempty ambientOpen]
  [divisorNonempty : Nonempty divisorOpen]
  ambientAffine : IsAffineOpen ambientOpen
  divisorAffine : IsAffineOpen divisorOpen
  inside : divisorOpen ≤ i.left ⁻¹ᵁ ambientOpen
  parameters : Fin (n+1) → Γ(P.variety.X.left,ambientOpen)
  quotient : RingHom.ker (i.left.appLE ambientOpen divisorOpen inside).hom =
    Ideal.span {parameters 0}
  surjective : Function.Surjective (i.left.appLE ambientOpen divisorOpen inside)
  sourceBasis : Module.Basis Unit (FunctionField P.variety) (RationalTopForms P.variety)
  sourceNormalized :
    letI := fractionAlgebra P.variety
    sourceBasis () = exteriorPower.ιMulti (FunctionField P.variety) (n+1)
      (fun j => KaehlerDifferential.D k (FunctionField P.variety)
        (P.variety.X.left.germToFunctionField ambientOpen (parameters j)))
  targetBasis : Module.Basis Unit (FunctionField S) (RationalTopForms S)
  targetNormalized :
    letI := fractionAlgebra S
    targetBasis () = exteriorPower.ιMulti (FunctionField S) n
      (fun j => KaehlerDifferential.D k (FunctionField S)
        (S.X.left.germToFunctionField divisorOpen
          (i.left.appLE ambientOpen divisorOpen inside (parameters j.succ))))
  sourceGenerator : Γ(A.line.val,ambientOpen)
  sourceGeneratorNormalized :
    rationalFunctionsEquiv ambientOpen (R.map.app ambientOpen sourceGenerator) =
      1 / ((sourceBasis.repr P.canonical.form () : FunctionField P.variety) *
        P.variety.X.left.germToFunctionField ambientOpen (parameters 0))^m
  pulledGenerates : ∀ x (hx : x ∈ divisorOpen),
    letI := moduleStalkModule S.X.left
      ((Scheme.Modules.pullback i.left).obj A.line.val) x
    Submodule.span (LocalRing S x)
      {TopCat.Presheaf.germ
        ((Scheme.Modules.pullback i.left).obj A.line.val).presheaf divisorOpen x hx
          (pullOpenSection i A.line.val ambientOpen divisorOpen inside sourceGenerator)} = ⊤

/-- Global residue comparison fixed by the actual chart generator and all Cartier generators. -/
structure ResidueComparison {P : LogPair k (n + 1)} {m : ℕ} {A : CartierLine P.variety}
    {S : NormalVariety k n} {C : CanonicalData S} {i : S.X ⟶ P.variety.X}
    {R : CartierRationalization A} (F : ResidueChart P m A S C i R) where
  cartier : CartierLine S
  moduleComparison : cartier.line.val ≅ (Scheme.Modules.pullback i.left).obj A.line.val
  residue : (Scheme.Modules.pullback i.left).obj A.line.val ⟶ rationalFunctions S.X.left
  chartNormalized :
    letI := F.divisorNonempty
    rationalFunctionsEquiv F.divisorOpen
      (residue.app F.divisorOpen (pullOpenSection i A.line.val
        F.ambientOpen F.divisorOpen F.inside F.sourceGenerator)) =
      1 / (F.targetBasis.repr C.form () : FunctionField S)^m
  generatorsNormalized : ∀ j,
    letI := cartier.nonempty j
    rationalFunctionsEquiv (cartier.opens j)
      (residue.app (cartier.opens j)
        (moduleComparison.hom.app (cartier.opens j) (cartier.sections j))) =
      (cartier.functions j : FunctionField S)⁻¹

/-- The adjunction different on the normalization `S` of the coefficient-one component, computed
from the fixed residue comparison: `(1/m) · div(residue) - K_S`. -/
def different {P : LogPair k (n + 1)} {m : ℕ} {A : CartierLine P.variety}
    {S : NormalVariety k n} {C : CanonicalData S} {i : S.X ⟶ P.variety.X}
    {R : CartierRationalization A} {F : ResidueChart P m A S C i R}
    (D : ResidueComparison F) : RealWeil S :=
  (1/(m : ℝ)) • realCast D.cartier.divisor - realCast (canonicalDivisor C)

/-- The actual affine conductor for the specified normalization ring map. -/
def ringConductor {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Ideal R :=
  letI := f.toAlgebra
  (_root_.conductor R (0 : S)).comap f

/-- The global conductor is pinned on every actual affine normalization section ring. -/
structure ConductorSheaf {X N : Scheme.{0}} (ν : N ⟶ X) where
  ideal : X.IdealSheafData
  normalized : ∀ U : X.affineOpens, ideal.ideal U = ringConductor (ν.app U.val).hom

end MathlibExt.AlgebraicGeometry.LogResidueDifferent
