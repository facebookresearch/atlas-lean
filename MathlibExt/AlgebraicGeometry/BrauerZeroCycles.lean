/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BrauerLocalInvariant
public import MathlibExt.AlgebraicGeometry.BrauerArithmeticCompletion
public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Native zero-cycle Brauer evaluation endpoints

The cycle carrier and rational equivalence quotient are the existing integral
scheme Chow definitions. Every coefficient is an integer, and every summand
uses the actual residue-field point and normalized field corestriction.

Harpaz--Wittenberg, arXiv:1409.0993v4, pp. 1--2, use the archimedean norm
cokernel and `lim_n CH₀/n`. Both quotient maps are fixed here. Descent of the
arithmetic evaluation through rational equivalence and archimedean norms is
recorded directly in `WantedExt`; this is not a new cycle carrier.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerZeroCycles

open CategoryTheory BrauerCoefficients BrauerEvaluation BrauerCorestriction
open BrauerInteroperability
open IntegerSchemeChow

variable {k : Type} [Field k] (X : FieldScheme k)

/-- The actual dimension-zero points of the integral cycle carrier. -/
abbrev ZeroPoint := {x : X.scheme.left // PointDimension X.scheme.left x 0}

/-- The scalar map to an actual residue field, from the structural scheme map. -/
def residueBaseMap (x : ZeroPoint X) : k →+* X.scheme.left.residueField x.val :=
  (X.scheme.left.Γevaluation x.val).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.scheme.hom.appTop).hom

/-- Data for transferring Brauer classes from the residue field $\kappa(x)$ of a dimension-zero
point $x$ of $X$ to $k$: a $k$-embedding `embedding` of $\kappa(x)$ into the separable closure of
$k$; a `FiniteFieldPair` for it, which identifies the separable closures and, compatibly with their
actions, the absolute Galois group of $\kappa(x)$ with the subgroup of that of $k$ fixing the image,
this subgroup being open of finite index; and a corestriction
$\mathrm{Br}(\kappa(x)) \to \mathrm{Br}(k)$ given on cocycle classes by the transfer formula
(`NormalizedCorestriction`). -/
structure ResidueFieldData (x : ZeroPoint X) where
  embedding :
    letI := (residueBaseMap X x).toAlgebra
    X.scheme.left.residueField x.val →ₐ[k] SeparableClosure k
  finitePair :
    letI := (residueBaseMap X x).toAlgebra
    FiniteFieldPair k (X.scheme.left.residueField x.val) embedding
  corestriction :
    letI := (residueBaseMap X x).toAlgebra
    NormalizedCorestriction k (X.scheme.left.residueField x.val) embedding finitePair

/-- Integer coordinates on the actual dimension-zero points.
Finite support follows from the compact scheme's locally finite cycle support. -/
def cycleCoordinates : CycleGroup X.scheme.left 0 →+ (ZeroPoint X →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite (fun x => c.val x.val)
    (c.val.finite_support.preimage Subtype.val_injective.injOn)
  map_zero' := by ext x; rfl
  map_add' c d := by ext x; rfl

/-- One summand is actual residue-point pullback, field comparison and transfer. -/
def residueEvaluation (B : FieldComparisonFamily)
    (D : ∀ x : ZeroPoint X, ResidueFieldData X x)
    (a : Brauer X.scheme.left) (x : ZeroPoint X) : Br k :=
  letI := (residueBaseMap X x).toAlgebra
  (D x).corestriction.val ((B (X.scheme.left.residueField x.val)).val
    (pointPullback (X.scheme.left.residueField x.val)
      (X.scheme.left.fromSpecResidueField x.val) a.val))

/-- Actual signed integer-cycle/corestriction evaluation. -/
def cycleEvaluation (B : FieldComparisonFamily)
    (D : ∀ x : ZeroPoint X, ResidueFieldData X x)
    (a : Brauer X.scheme.left) : CycleGroup X.scheme.left 0 →+ Br k :=
  (Finsupp.linearCombination ℤ (residueEvaluation X B D a)).toAddMonoidHom.comp
    (cycleCoordinates X)

/-- The type of additive maps $f : \mathrm{CH}_0(X) \to \mathrm{Br}(k)$ sending the class of every
zero-cycle $c$ to `cycleEvaluation X B D a c`: factorizations through rational equivalence of the
evaluation of the Brauer class $a$ on zero-cycles, for the field comparisons $B$ and the
residue-field data $D$. -/
abbrev ChowEvaluation (B : FieldComparisonFamily)
    (D : ∀ x : ZeroPoint X, ResidueFieldData X x)
    (a : Brauer X.scheme.left) :=
  {f : ChowGroup X 0 →+ Br k //
    ∀ c : CycleGroup X.scheme.left 0,
      f (cycleClass X 0 c) = cycleEvaluation X B D a c}

section Norm

variable {l : Type} [Field l] (Y : FieldScheme l) (i : k →+* l)

/-- An actual base-change square of field schemes along a finite field extension `i`, so that
`map` is finite, hence proper. -/
structure CartesianFieldExtension where
  /-- The base-change map `Y = X ×_k l → X`. -/
  map : Y.scheme.left ⟶ X.scheme.left
  cartesian : IsPullback map Y.scheme.hom X.scheme.hom (Spec.map (CommRingCat.ofHom i))
  /-- The field extension is finite. -/
  finite : i.Finite

/-- The type of additive maps $N : \mathrm{CH}_0(Y) \to \mathrm{CH}_0(X)$ sending the class of every
zero-cycle $c$ on $Y$ to the class of the dimension-zero part of the pushforward of $c$ (with
residue-degree multiplicities) along the base-change map `E.map`. -/
abbrev NormalizedNorm (E : CartesianFieldExtension X Y i) :=
  {N : ChowGroup Y 0 →+ ChowGroup X 0 //
    ∀ c : CycleGroup Y.scheme.left 0,
      N (cycleClass Y 0 c) = cycleClass X 0
        (dimensionPart X.scheme.left 0
          (AlgebraicCycle.map E.map Order.height Order.height c.val))}

/-- The actual archimedean modification is the norm cokernel. -/
abbrev NormQuotient (E : CartesianFieldExtension X Y i) (N : NormalizedNorm X Y i E) :=
  ChowGroup X 0 ⧸ N.val.range

/-- The map to the norm cokernel is the actual quotient map. -/
def normQuotientMap (E : CartesianFieldExtension X Y i) (N : NormalizedNorm X Y i E) :
    ChowGroup X 0 →+ NormQuotient X Y i E N := QuotientAddGroup.mk' N.val.range

/-- The exact arithmetic completion of the modified group. -/
abbrev CompletedNormQuotient (E : CartesianFieldExtension X Y i)
    (N : NormalizedNorm X Y i E) :=
  BrauerArithmeticCompletion.Completion (NormQuotient X Y i E N)

end Norm

/-- The exact `lim_n CH₀/n` endpoint of the arithmetic complex. -/
abbrev CompletedChow := BrauerArithmeticCompletion.Completion (ChowGroup X 0)

end AlgebraicGeometry.BrauerZeroCycles
