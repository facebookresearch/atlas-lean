/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLoopTests
public import MathlibExt.LinearAlgebra.LocalizedLattices
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Finite-projective lattices on every perfect residue-algebra test

The integral ring is the original `W(R) tensor W(k) B`, and the ambient
module is its actual uniformizer localization to the power `n`. A lattice
is a finite-projective full-rank submodule with its canonical localization
map. No nonzero-ring condition is imposed on a perfect test algebra.

Scalar extension is fixed by the span of the images under the actual
localized Witt tensor map. Matrix actions are fixed by the native linear
equivalence of an invertible matrix. The output dictionaries below retain
all identity, composition and bounded-transition laws; their construction
is requested separately, with the genuine coefficient hypotheses.

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), pp. 2--3,
Sections 0.5 and 1.2.1, pp. 6--9. These are completed object and map
definitions, not an ind-representability or Satake proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels

open CategoryTheory
open RelativeWittLoopTests
open MathlibExt.LinearAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)

/-- The uniformizer is the image of the original coefficient element. -/
abbrev parameter (R : PerfectAlgebra p k) : Integral p k B R :=
  coefficient p k B R pi

/-- Actual finite-projective submodules of the original localized module. -/
abbrev Lattice (R : PerfectAlgebra p k) (n : ℕ) :=
  LocalizedLattices.Lattice (Integral p k B R) (parameter p k B pi R) n

/-- The actual two-sided uniformizer bounds, rather than a Schubert oracle. -/
abbrev BoundedLattice (R : PerfectAlgebra p k) (n N : ℕ) :=
  {L : Lattice p k B pi R n //
    LocalizedLattices.IsBoundedBy _ _ _ L N}

/-- The underlying scalar map acts on every original localized coordinate. -/
def coordinateSpan {R S : PerfectAlgebra p k} (f : R ⟶ S)
    {n : ℕ} (L : Lattice p k B pi R n) :
    Submodule (Integral p k B S) (Fin n → Rational p k B pi S) :=
  Submodule.span _ {v | ∃ x : L.module,
    v = fun i ↦ rationalMap p k B pi f (x.val i)}

/-- A normalized output dictionary for the actual lattice scalar extensions. -/
structure ScalarExtension (n : ℕ) where
  map : ∀ {R S : PerfectAlgebra p k}, (R ⟶ S) →
    Lattice p k B pi R n → Lattice p k B pi S n
  image : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (L : Lattice p k B pi R n), (map f L).module = coordinateSpan p k B pi f L
  map_id : ∀ (R : PerfectAlgebra p k) (L : Lattice p k B pi R n), map (𝟙 R) L = L
  map_comp : ∀ {R S T : PerfectAlgebra p k} (f : R ⟶ S) (g : S ⟶ T)
    (L : Lattice p k B pi R n), map (f ≫ g) L = map g (map f L)
  bounded : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (L : Lattice p k B pi R n) (N : ℕ),
    LocalizedLattices.IsBoundedBy _ _ _ L N →
      LocalizedLattices.IsBoundedBy _ _ _ (map f L) N
  increasing : ∀ (R : PerfectAlgebra p k) (L : Lattice p k B pi R n)
    {N M : ℕ}, N ≤ M → LocalizedLattices.IsBoundedBy _ _ _ L N →
      LocalizedLattices.IsBoundedBy _ _ _ L M

variable {p k B pi}

/-- The lattice functor uses the prescribed scalar extension on every arrow. -/
def ScalarExtension.functor {n : ℕ} (D : ScalarExtension p k B pi n) :
    PerfectAlgebra p k ⥤ Type 1 where
  obj R := ULift.{1} (Lattice p k B pi R n)
  map f := ↾fun L ↦ ULift.up (D.map f L.down)
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    exact D.map_id R L.down
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    exact D.map_comp f g L.down

/-- Every bounded subfunctor uses the same original Witt scalar map. -/
def ScalarExtension.boundedFunctor {n : ℕ} (D : ScalarExtension p k B pi n)
    (N : ℕ) : PerfectAlgebra p k ⥤ Type 1 where
  obj R := ULift.{1} (BoundedLattice p k B pi R n N)
  map f := ↾fun L ↦ ULift.up
    ⟨D.map f L.down.val, D.bounded f L.down.val N L.down.property⟩
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    apply Subtype.ext
    exact D.map_id R L.down.val
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    apply Subtype.ext
    exact D.map_comp f g L.down.val

/-- Transition maps retain the very same lattice submodule. -/
def ScalarExtension.transition {n N M : ℕ} (D : ScalarExtension p k B pi n)
    (h : N ≤ M) : D.boundedFunctor N ⟶ D.boundedFunctor M where
  app R := ↾fun L ↦ ULift.up
    ⟨L.down.val, D.increasing R L.down.val h L.down.property⟩
  naturality {R S} f := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    apply Subtype.ext
    rfl

variable (p k B pi)

/-- The native invertible-matrix action on the original ambient module. -/
def matrixTransform (R : PerfectAlgebra p k) (n : ℕ)
    (g : GL (Fin n) (Rational p k B pi R)) :
    (Fin n → Rational p k B pi R) ≃ₗ[Integral p k B R]
      (Fin n → Rational p k B pi R) :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.restrictScalars _

/-- Matrix action is the actual image submodule under that equivalence. -/
def matrixImage (R : PerfectAlgebra p k) {n : ℕ}
    (g : GL (Fin n) (Rational p k B pi R)) (L : Lattice p k B pi R n) :
    Submodule (Integral p k B R) (Fin n → Rational p k B pi R) :=
  L.module.map (matrixTransform p k B pi R n g).toLinearMap

/-- The standard-lattice orbit uses the original integral free-module image. -/
def standardOrbit (R : PerfectAlgebra p k) (n : ℕ)
    (g : GL (Fin n) (Rational p k B pi R)) :
    Submodule (Integral p k B R) (Fin n → Rational p k B pi R) :=
  (LocalizedLattices.standard _ (parameter p k B pi R) n).map
    (matrixTransform p k B pi R n g).toLinearMap

/-- An action of invertible matrices on rank-$n$ lattices compatible with the scalar extension $D$.
Here $p$ is a prime, $k$ a commutative ring, $B$ a commutative $W(k)$-algebra and $\pi \in B$; for
a perfect $k$-algebra $R$, lattices are finite projective full-rank submodules of
$((W(R) \otimes_{W(k)} B)[1/\pi])^n$, and $\mathrm{GL}_n$ is taken over that localized ring. It
consists of, for every perfect $k$-algebra $R$, an action `act` of $\mathrm{GL}_n$ on lattices,
sending a lattice to its image under the matrix, and a lattice `standard R` whose module is the
standard lattice, such that the scalar extensions of $D$ send standard lattices to standard
lattices, the images of matrices in $\mathrm{GL}_n(W(R) \otimes_{W(k)} B)$ (invertible over the
integral ring, not only over its localization) fix the standard lattice and preserve every bound
$N$, and the action commutes with scalar extension along every map $R \to S$. -/
structure MatrixAction (n : ℕ) (D : ScalarExtension p k B pi n) where
  act : ∀ (R : PerfectAlgebra p k), GL (Fin n) (Rational p k B pi R) →
    Lattice p k B pi R n → Lattice p k B pi R n
  image : ∀ R g L, (act R g L).module = matrixImage p k B pi R g L
  one : ∀ R L, act R 1 L = L
  mul : ∀ R g h L, act R (g * h) L = act R g (act R h L)
  standard : ∀ R : PerfectAlgebra p k, Lattice p k B pi R n
  standard_image : ∀ R, (standard R).module =
    LocalizedLattices.standard _ (parameter p k B pi R) n
  standard_naturality : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S),
    D.map f (standard R) = standard S
  positive_standard : ∀ (R : PerfectAlgebra p k)
    (h : GL (Fin n) (Integral p k B R)),
    act R (Matrix.GeneralLinearGroup.map (algebraMap _ _) h) (standard R) = standard R
  positive_bounded : ∀ (R : PerfectAlgebra p k)
    (h : GL (Fin n) (Integral p k B R)) (L : Lattice p k B pi R n) (N : ℕ),
    LocalizedLattices.IsBoundedBy _ _ _ L N →
      LocalizedLattices.IsBoundedBy _ _ _
        (act R (Matrix.GeneralLinearGroup.map (algebraMap _ _) h) L) N
  naturality : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (g : GL (Fin n) (Rational p k B pi R)) (L : Lattice p k B pi R n),
    D.map f (act R g L) =
      act S (Matrix.GeneralLinearGroup.map (rationalMap p k B pi f) g) (D.map f L)

end MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
