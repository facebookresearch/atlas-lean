/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The original W(R) lattice functor and its unramified tensor normalization

The unramified integral tensor ring is identified with `W(R)` by the
native right-unit tensor equivalence. The rational equivalence is its
actual localization at p. Both comparisons commute with the original
Witt-vector maps on every perfect k-algebra, including zero.

The direct lattice object is literally a finite-projective `W(R)`
submodule of `W(R)[1/p]^n`, with its canonical localization map. A
lattice transport is fixed by those actual coordinate equivalences;
its direct functor uses the original Witt maps, not an unrelated functor.

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), pp. 2--3,
and Section 1.2.1, p. 9. The tensor/localization ring maps are completed
native proofs. The normalized lattice transport remains a separate
construction request.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization

open _root_.CategoryTheory
open RelativeWittLoopTests
open MathlibExt.LinearAlgebra
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

attribute [local instance] wittAlgebra

/-- The actual tensor right-unit equivalence, with the original Witt scalars. -/
def integralEquiv (R : PerfectAlgebra p k) :
    Integral p k (WittVector p k) R ≃+* WittVector p R.obj :=
  (Algebra.TensorProduct.rid (WittVector p k) (WittVector p k)
    (WittVector p R.obj)).toRingEquiv

/-- Every original pure tensor has its actual scalar-product image. -/
theorem integralEquiv_tensor (R : PerfectAlgebra p k)
    (w : WittVector p R.obj) (b : WittVector p k) :
    integralEquiv p k R (tensor p k (WittVector p k) R w b) =
      wittScalars p k R b * w := by
  change b • w = wittScalars p k R b * w
  rfl

/-- Original coefficient elements have their prescribed Witt-scalar image. -/
theorem integralEquiv_coefficient (R : PerfectAlgebra p k) (b : WittVector p k) :
    integralEquiv p k R (coefficient p k (WittVector p k) R b) =
      wittScalars p k R b := by
  change integralEquiv p k R (tensor p k (WittVector p k) R 1 b) = _
  rw [integralEquiv_tensor, mul_one]

/-- The tensor right-unit comparison retains the actual Witt base-change square. -/
theorem integralEquiv_naturality {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (a : Integral p k (WittVector p k) R) :
    integralEquiv p k S (integralMap p k (WittVector p k) f a) =
      WittVector.map f.hom.hom.toRingHom (integralEquiv p k R a) := by
  have h : (integralEquiv p k S).toRingHom.comp
      (integralMap p k (WittVector p k) f) =
        (WittVector.map f.hom.hom.toRingHom).comp (integralEquiv p k R).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro w
      change integralEquiv p k S
        (tensor p k (WittVector p k) S (WittVector.map f.hom.hom.toRingHom w) 1) =
          WittVector.map f.hom.hom.toRingHom
            (integralEquiv p k R (tensor p k (WittVector p k) R w 1))
      rw [integralEquiv_tensor, integralEquiv_tensor]
      simp only [map_one, one_mul]
    · apply RingHom.ext
      intro b
      change integralEquiv p k S
        (integralMap p k (WittVector p k) f (coefficient p k (WittVector p k) R b)) =
          WittVector.map f.hom.hom.toRingHom
            (integralEquiv p k R (coefficient p k (WittVector p k) R b))
      rw [integralMap_coefficient, integralEquiv_coefficient, integralEquiv_coefficient]
      exact ((wittMap p k f).commutes b).symm
  exact RingHom.congr_fun h a

/-- The localization equivalence inverts precisely the same original p. -/
def rationalEquiv (R : PerfectAlgebra p k) :
    Rational p k (WittVector p k) (p : WittVector p k) R ≃+*
      Localization.Away (p : WittVector p R.obj) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coefficient p k (WittVector p k) R (p : WittVector p k)))
    (T := Submonoid.powers (p : WittVector p R.obj))
    (Rational p k (WittVector p k) (p : WittVector p k) R)
    (Localization.Away (p : WittVector p R.obj)) (integralEquiv p k R) (by
    rw [Submonoid.map_powers]
    congr 1
    change integralEquiv p k R
      (coefficient p k (WittVector p k) R (p : WittVector p k)) =
      (p : WittVector p R.obj)
    simp only [map_natCast])

/-- The rational equivalence extends the original integral tensor equivalence. -/
theorem rationalEquiv_unit (R : PerfectAlgebra p k)
    (a : Integral p k (WittVector p k) R) :
    rationalEquiv p k R (algebraMap _ _ a) =
      algebraMap _ _ (integralEquiv p k R a) := by
  unfold rationalEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

/-- The direct W(R)[1/p] map is the actual localized Witt-vector map. -/
def directRationalMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    Localization.Away (p : WittVector p R.obj) →+*
      Localization.Away (p : WittVector p S.obj) :=
  Localization.awayLift
    ((algebraMap (WittVector p S.obj)
      (Localization.Away (p : WittVector p S.obj))).comp
        (WittVector.map f.hom.hom.toRingHom)) (p : WittVector p R.obj) (by
    have h : IsUnit (algebraMap (WittVector p S.obj)
        (Localization.Away (p : WittVector p S.obj)) (p : WittVector p S.obj)) :=
      IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (p : WittVector p S.obj)) _
    simpa only [RingHom.comp_apply, map_natCast] using h)

/-- Direct localized coordinates retain their actual integral Witt-map image. -/
theorem directRationalMap_unit {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (w : WittVector p R.obj) :
    directRationalMap p k f (algebraMap _ _ w) =
      algebraMap _ _ (WittVector.map f.hom.hom.toRingHom w) := by
  simp only [directRationalMap, Localization.awayLift, IsLocalization.Away.lift_eq,
    RingHom.comp_apply]

/-- Both p-localized descriptions retain the full original Witt base-change map. -/
theorem rationalEquiv_naturality {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (a : Rational p k (WittVector p k) (p : WittVector p k) R) :
    rationalEquiv p k S (rationalMap p k (WittVector p k) (p : WittVector p k) f a) =
      directRationalMap p k f (rationalEquiv p k R a) := by
  have h : (rationalEquiv p k S).toRingHom.comp
      (rationalMap p k (WittVector p k) (p : WittVector p k) f) =
        (directRationalMap p k f).comp (rationalEquiv p k R).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (coefficient p k (WittVector p k) R (p : WittVector p k)))
    apply RingHom.ext
    intro b
    change rationalEquiv p k S
      (rationalMap p k (WittVector p k) (p : WittVector p k) f (algebraMap _ _ b)) =
        directRationalMap p k f (rationalEquiv p k R (algebraMap _ _ b))
    rw [rationalMap_unit, rationalEquiv_unit, rationalEquiv_unit, directRationalMap_unit]
    exact congrArg (algebraMap (WittVector p S.obj) _)
      (integralEquiv_naturality p k f b)
  exact RingHom.congr_fun h a

/-- The direct source lattice, on every actual perfect k-algebra. -/
abbrev WittLattice (R : PerfectAlgebra p k) (n : ℕ) :=
  LocalizedLattices.Lattice (WittVector p R.obj) (p : WittVector p R.obj) n

/-- The prescribed direct W(R)-scalar extension image. -/
def directCoordinateSpan {R S : PerfectAlgebra p k} (f : R ⟶ S)
    {n : ℕ} (L : WittLattice p k R n) :
    Submodule (WittVector p S.obj) (Fin n → Localization.Away (p : WittVector p S.obj)) :=
  Submodule.span _ {v | ∃ x : L.module,
    v = fun i ↦ directRationalMap p k f (x.val i)}

variable (n : ℕ)
  (D : RelativeWittLatticeModels.ScalarExtension p k (WittVector p k)
    (p : WittVector p k) n)

/-- Lattice transport is fixed by actual normalized coordinate images. -/
structure LatticeComparison where
  lattice : ∀ R : PerfectAlgebra p k,
    RelativeWittLatticeModels.Lattice p k (WittVector p k) (p : WittVector p k) R n ≃
      WittLattice p k R n
  coordinates : ∀ (R : PerfectAlgebra p k)
    (L : RelativeWittLatticeModels.Lattice p k (WittVector p k) (p : WittVector p k) R n)
    (v : Fin n → Localization.Away (p : WittVector p R.obj)),
    v ∈ (lattice R L).module ↔
      ∃ x : L.module, v = fun i ↦ rationalEquiv p k R (x.val i)
  base_change_image : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (L : RelativeWittLatticeModels.Lattice p k (WittVector p k) (p : WittVector p k) R n),
    (lattice S (D.map f L)).module = directCoordinateSpan p k f (lattice R L)
  bounds : ∀ (R : PerfectAlgebra p k)
    (L : RelativeWittLatticeModels.Lattice p k (WittVector p k) (p : WittVector p k) R n)
    (N : ℕ), LocalizedLattices.IsBoundedBy _ _ _ L N ↔
      LocalizedLattices.IsBoundedBy _ _ _ (lattice R L) N

variable {p k n D}

/-- The actual direct Witt-lattice functor, conjugating only the fixed ring transport. -/
def LatticeComparison.functor (E : LatticeComparison p k n D) :
    PerfectAlgebra p k ⥤ Type 1 where
  obj R := ULift.{1} (WittLattice p k R n)
  map {R S} f := ↾fun L ↦
    ULift.up (E.lattice S (D.map f ((E.lattice R).symm L.down)))
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    change E.lattice R (D.map (𝟙 R) ((E.lattice R).symm L.down)) = L.down
    rw [D.map_id, Equiv.apply_symm_apply]
  map_comp {R S T} f g := by
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    change E.lattice T (D.map (f ≫ g) ((E.lattice R).symm L.down)) =
      E.lattice T (D.map g ((E.lattice S).symm
        (E.lattice S (D.map f ((E.lattice R).symm L.down)))))
    rw [D.map_comp, Equiv.symm_apply_apply]

variable (p k n)

/-- The source constructor supplies the actual direct functor and matrix actions together. -/
structure UnramifiedModel where
  extension : RelativeWittLatticeModels.ScalarExtension p k (WittVector p k)
    (p : WittVector p k) n
  comparison : LatticeComparison p k n extension
  matrix : RelativeWittLatticeModels.MatrixAction p k (WittVector p k)
    (p : WittVector p k) n extension

variable {p k n}

/-- The direct source functor on every perfect k-algebra, including zero. -/
def UnramifiedModel.functor (E : UnramifiedModel p k n) := E.comparison.functor

/-- Direct localized matrices act through the actual proved rational ring equivalence. -/
def UnramifiedModel.act (E : UnramifiedModel p k n) (R : PerfectAlgebra p k)
    (g : GL (Fin n) (Localization.Away (p : WittVector p R.obj)))
    (L : WittLattice p k R n) : WittLattice p k R n :=
  E.comparison.lattice R
    (E.matrix.act R (Matrix.GeneralLinearGroup.map (rationalEquiv p k R).symm.toRingHom g)
      ((E.comparison.lattice R).symm L))

/-- The direct bounded lattice object retains the two original p-power inclusions. -/
abbrev BoundedWittLattice (R : PerfectAlgebra p k) (n N : ℕ) :=
  {L : WittLattice p k R n // LocalizedLattices.IsBoundedBy _ _ _ L N}

end MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
