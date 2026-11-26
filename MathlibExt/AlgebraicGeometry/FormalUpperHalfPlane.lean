/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings.lean`,
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean`,
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum.lean`
and `Definitions/Def_LatticeTreeOrbital.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor
public import MathlibExt.AlgebraicGeometry.FormalOmega.DeligneDatum

/-!
# Charts of the formal upper half plane

The functors of this file go from commutative `𝒪`-algebras to types: they are functors
`CommAlgCat 𝒪 ⥤ Type`, maps between them are natural transformations, and corepresentability is
`Functor.CorepresentableBy`.

* `chartV 𝒪 q`: the vertex chart, the points `ζ` with `ζ ^ q - ζ` a unit.
* `chartE 𝒪 π q`: the edge chart, the pairs `(ξ, η)` with `ξ * η = π` and with `ξ ^ (q - 1) - 1`
  and `η ^ (q - 1) - 1` units.
* `vertexToEdge`: the transition `ζ ↦ (ζ, π ζ⁻¹)` from the unit vertex chart `chartVUnit 𝒪 q` to
  the edge chart, defined on the algebras in which `π` is nilpotent and natural among them
  (`vertexToEdge_natural`).
* `chartVRing R q` and `chartERing R π q`: localizations of polynomial rings that corepresent the
  two charts; `chartVRing.corepIso` and `chartERing.corepIso` are the natural isomorphisms from
  the functors of algebra maps out of these rings.
* `OmegaNrObj` and `OmegaNr.IsTwistedAct`: pairs of an `Onr`-point and a Deligne datum of
  `MathlibExt.AlgebraicGeometry.FormalOmega.DeligneDatum`, and the relation saying that `x'` is
  obtained from `x` by `g ∈ GL₂(K)`: the point is twisted by `frobTwist` (from
  `MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor`) with exponent `-vdet g`,
  and the datum is pulled back along `g⁻¹`. The automorphism `Fr` and the hom `vdet` are supplied
  data, and this module does not prove that the relation is a group action.
-/

@[expose] public section

open scoped CategoryTheory

namespace CerednikDrinfeld
namespace FormalOmega

section NatTrans

variable {𝒪 : Type} [CommRing 𝒪]

def IsIsoOnNilp (π : 𝒪) {F G : CommAlgCat.{0} 𝒪 ⥤ Type} (η : F ⟶ G) : Prop :=
  ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) → Function.Bijective (η.app B)

def IsMonoOnNilp (π : 𝒪) {F G : CommAlgCat.{0} 𝒪 ⥤ Type} (η : F ⟶ G) : Prop :=
  ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) → Function.Injective (η.app B)

end NatTrans

section Charts

variable (𝒪 : Type) [CommRing 𝒪]

def chartV (q : ℕ) : CommAlgCat.{0} 𝒪 ⥤ Type where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) }
  map f := TypeCat.ofHom fun x => ⟨f.hom x.1, by
    have h := x.2.map f.hom
    rwa [map_sub, map_pow] at h⟩

def chartE (π : 𝒪) (q : ℕ) : CommAlgCat.{0} 𝒪 ⥤ Type where
  obj B := { p : B × B // p.1 * p.2 = algebraMap 𝒪 B π ∧ IsUnit (p.1 ^ (q - 1) - 1) ∧ IsUnit (p.2 ^
    (q - 1) - 1) }
  map f := TypeCat.ofHom fun x => ⟨(f.hom x.1.1, f.hom x.1.2), by
    obtain ⟨h₁, h₂, h₃⟩ := x.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, h₁, AlgHom.commutes]
    · have h := h₂.map f.hom
      rwa [map_sub, map_pow, map_one] at h
    · have h := h₃.map f.hom
      rwa [map_sub, map_pow, map_one] at h⟩

def chartVUnit (q : ℕ) : CommAlgCat.{0} 𝒪 ⥤ Type where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) ∧ IsUnit ζ }
  map f := TypeCat.ofHom fun x => ⟨f.hom x.1, by
    obtain ⟨h₁, h₂⟩ := x.2
    refine ⟨?_, h₂.map f.hom⟩
    have h := h₁.map f.hom
    rwa [map_sub, map_pow] at h⟩

def chartVUnitIncl (q : ℕ) : chartVUnit 𝒪 q ⟶ chartV 𝒪 q where
  app _ := TypeCat.ofHom fun x => ⟨x.1, x.2.1⟩

variable {𝒪}

theorem isUnit_pow_pred_sub_one_of_isUnit_pow_sub {B : Type} [CommRing B] {q : ℕ} (hq : 1 ≤ q) {ζ :
  B}
    (h : IsUnit (ζ ^ q - ζ)) : IsUnit (ζ ^ (q - 1) - 1) := by
  have hpow : ζ ^ q = ζ ^ (q - 1) * ζ := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  have hfac : ζ ^ q - ζ = ζ * (ζ ^ (q - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac] at h
  exact isUnit_of_mul_isUnit_right h

theorem isUnit_pow_succ_sub_one_of_isNilpotent {B : Type} [CommRing B] {a : B} (ha : IsNilpotent a)
  (b : B) (n : ℕ) :
    IsUnit ((a * b) ^ (n + 1) - 1) := by
  have hab : IsNilpotent (a * b) := Commute.isNilpotent_mul_right (Commute.all a b) ha
  have hpow : IsNilpotent ((a * b) ^ (n + 1)) := by
    obtain ⟨m, hm⟩ := hab
    exact ⟨m, by rw [← pow_mul, Nat.mul_comm (n + 1) m, pow_mul, hm, zero_pow (Nat.succ_ne_zero n)]⟩
  exact hpow.isUnit_sub_one

noncomputable def vertexToEdge (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) (B : CommAlgCat.{0} 𝒪)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (chartVUnit 𝒪 q).obj B) : (chartE 𝒪 π q).obj B :=
  ⟨(x.1, algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)), by
    refine ⟨?_, ?_, ?_⟩
    · calc x.1 * (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹))
          = algebraMap 𝒪 B π * (x.1 * ↑(x.2.2.unit⁻¹)) := by ring
        _ = algebraMap 𝒪 B π := by rw [IsUnit.mul_val_inv, mul_one]
    · exact isUnit_pow_pred_sub_one_of_isUnit_pow_sub (le_trans (by norm_num) hq) x.2.1
    · obtain ⟨n, hn⟩ : ∃ n, q - 1 = n + 1 := ⟨q - 2, by omega⟩
      rw [hn]
      exact isUnit_pow_succ_sub_one_of_isNilpotent hB _ n⟩

theorem vertexToEdge_natural (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) {B B' : CommAlgCat.{0} 𝒪}
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (f : B ⟶ B')
    (x : (chartVUnit 𝒪 q).obj B) :
    (chartE 𝒪 π q).map f (vertexToEdge π hq B hB x) =
      vertexToEdge π hq B' hB' ((chartVUnit 𝒪 q).map f x) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change f.hom (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)) =
    algebraMap 𝒪 B' π * ↑(((chartVUnit 𝒪 q).map f x).2.2.unit⁻¹)
  rw [map_mul, AlgHom.commutes]
  congr 1
  have h1 : f.hom x.1 * f.hom ↑(x.2.2.unit⁻¹) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : f.hom x.1 * ↑(((chartVUnit 𝒪 q).map f x).2.2.unit⁻¹) = 1 :=
    IsUnit.mul_val_inv _
  exact (IsUnit.mul_right_injective (x.2.2.map f.hom)) (h1.trans h2.symm)

end Charts

section PadicInstance

variable (r : ℕ) [Fact r.Prime]

noncomputable abbrev padicChartV : CommAlgCat.{0} ℤ_[r] ⥤ Type := chartV ℤ_[r] r

noncomputable abbrev padicChartE : CommAlgCat.{0} ℤ_[r] ⥤ Type := chartE ℤ_[r] (r : ℤ_[r]) r

def SpecialFibreVertexChartShape : Prop :=
  ∀ (𝔽 : Type) [Field 𝔽] [Algebra ℤ_[r] 𝔽] [CharP 𝔽 r] (ζ : 𝔽),
    IsUnit (ζ ^ r - ζ) ↔ ∀ a : ZMod r, (ζ : 𝔽) ≠ (a.cast : 𝔽)

end PadicInstance

end FormalOmega
end CerednikDrinfeld

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]

abbrev vertexDiscr (q : ℕ) : R[X] := X ^ q - X

abbrev chartVRing (q : ℕ) : Type := Localization.Away (vertexDiscr R q)

namespace chartVRing

variable (q : ℕ)

def ζ : chartVRing R q := algebraMap R[X] (chartVRing R q) X

theorem algebraMap_vertexDiscr : algebraMap R[X] (chartVRing R q) (vertexDiscr R q) = ζ R q ^ q - ζ
  R q := by
  change algebraMap R[X] (chartVRing R q) (X ^ q - X) = _
  rw [map_sub, map_pow]; rfl

theorem isUnit_ζ_pow_sub : IsUnit (ζ R q ^ q - ζ R q) := by
  rw [← algebraMap_vertexDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (vertexDiscr R q)

def point : (chartV R q).obj (CommAlgCat.of R (chartVRing R q)) := ⟨ζ R q, isUnit_ζ_pow_sub R q⟩

variable {R q}

theorem isUnit_aeval_of_mem_powers {B : CommAlgCat.{0} R} (x : (chartV R q).obj B)
    (y : Submonoid.powers (vertexDiscr R q)) : IsUnit (Polynomial.aeval (R := R) x.1 (y : R[X])) :=
      by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  have : Polynomial.aeval (R := R) x.1 (vertexDiscr R q) = x.1 ^ q - x.1 := by
    change Polynomial.aeval (R := R) x.1 (X ^ q - X) = _
    rw [map_sub (Polynomial.aeval (R := R) x.1), map_pow (Polynomial.aeval (R := R) x.1),
      Polynomial.aeval_X]
  rw [this]; exact x.2

def lift {B : CommAlgCat.{0} R} (x : (chartV R q).obj B) : chartVRing R q →ₐ[R] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (vertexDiscr R q)) (f := Polynomial.aeval (R :=
    R) x.1)
    (isUnit_aeval_of_mem_powers x)

@[simp] theorem lift_ζ {B : CommAlgCat.{0} R} (x : (chartV R q).obj B) : lift x (ζ R q) = x.1 := by
  rw [lift, IsLocalization.liftAlgHom_apply, ζ, IsLocalization.lift_eq]
  exact Polynomial.aeval_X x.1

variable (R q) in
def corepEquiv (B : CommAlgCat.{0} R) : (chartVRing R q →ₐ[R] B) ≃ (chartV R q).obj B where
  toFun φ := (chartV R q).map (CommAlgCat.ofHom φ) (point R q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (vertexDiscr R q))
    apply Polynomial.algHom_ext
    change lift ((chartV R q).map (CommAlgCat.ofHom φ) (point R q)) (algebraMap R[X] _ X) =
      φ (algebraMap R[X] _ X)
    exact lift_ζ _
  right_inv x := Subtype.ext (lift_ζ x)

@[simp] theorem corepEquiv_apply_val (B : CommAlgCat.{0} R) (φ : chartVRing R q →ₐ[R] B) :
    (corepEquiv R q B φ).1 = φ (ζ R q) := rfl

theorem corepEquiv_natural {B B' : CommAlgCat.{0} R} (f : B ⟶ B') (φ : chartVRing R q →ₐ[R] B) :
    corepEquiv R q B' (f.hom.comp φ) = (chartV R q).map f (corepEquiv R q B φ) :=
  Subtype.ext rfl

variable (R q) in
def corepresentableBy : (chartV R q).CorepresentableBy (CommAlgCat.of R (chartVRing R q)) where
  homEquiv {B} := CategoryTheory.ConcreteCategory.homEquiv.trans (corepEquiv R q B)
  homEquiv_comp g f := by exact corepEquiv_natural g f.hom

variable (R q) in
def corepIso :
    CategoryTheory.coyoneda.obj (Opposite.op (CommAlgCat.of R (chartVRing R q))) ≅ chartV R q :=
  (corepresentableBy R q).toIso

theorem corepIso_hom_app_val (B : CommAlgCat.{0} R)
    (φ : CommAlgCat.of R (chartVRing R q) ⟶ B) :
    ((corepIso R q).hom.app B φ).1 = φ.hom (ζ R q) := rfl

theorem corepIso_inv_app (B : CommAlgCat.{0} R) (x : (chartV R q).obj B) :
    (corepIso R q).inv.app B x = CommAlgCat.ofHom (lift x) := rfl

end chartVRing

abbrev edgeRel (π : R) : MvPolynomial (Fin 2) R := MvPolynomial.X 0 * MvPolynomial.X 1 -
  MvPolynomial.C π

def edgeQuot (π : R) : Type := MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}

instance edgeQuot.instCommRing (π : R) : CommRing (edgeQuot R π) :=
  show CommRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance

instance edgeQuot.instAlgebra (π : R) : Algebra R (edgeQuot R π) :=
  show Algebra R (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance

def edgeQuot.mk (π : R) : MvPolynomial (Fin 2) R →ₐ[R] edgeQuot R π :=
  Ideal.Quotient.mkₐ R (Ideal.span {edgeRel R π})

theorem edgeQuot.mk_edgeRel (π : R) : edgeQuot.mk R π (edgeRel R π) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

abbrev edgeDiscr (q : ℕ) : MvPolynomial (Fin 2) R :=
  (MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)

def edgeQuot.discr (π : R) (q : ℕ) : edgeQuot R π := edgeQuot.mk R π (edgeDiscr R q)

abbrev chartERing (π : R) (q : ℕ) : Type := Localization.Away (edgeQuot.discr R π q)

namespace chartERing

variable (π : R) (q : ℕ)

def ofPoly : MvPolynomial (Fin 2) R →ₐ[R] chartERing R π q :=
  (Algebra.algHom R (edgeQuot R π) (chartERing R π q)).comp (edgeQuot.mk R π)

def ξ : chartERing R π q := ofPoly R π q (MvPolynomial.X 0)

def η : chartERing R π q := ofPoly R π q (MvPolynomial.X 1)

theorem ofPoly_edgeRel : ofPoly R π q (edgeRel R π) = 0 := by
  rw [ofPoly, AlgHom.comp_apply, edgeQuot.mk_edgeRel, map_zero]

theorem ξ_mul_η : ξ R π q * η R π q = algebraMap R (chartERing R π q) π := by
  have hC : ofPoly R π q (MvPolynomial.C π) = algebraMap R (chartERing R π q) π := (ofPoly R π
    q).commutes π
  have h2 : ofPoly R π q (edgeRel R π) = ξ R π q * η R π q - algebraMap R (chartERing R π q) π := by
    change ofPoly R π q (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = _
    rw [map_sub (ofPoly R π q), map_mul (ofPoly R π q), hC]; rfl
  rw [← sub_eq_zero, ← h2, ofPoly_edgeRel]

theorem ofPoly_edgeDiscr :
    ofPoly R π q (edgeDiscr R q) = (ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1) := by
  change ofPoly R π q ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)) = _
  rw [map_mul (ofPoly R π q), map_sub (ofPoly R π q), map_sub (ofPoly R π q), map_pow (ofPoly R π
    q),
    map_pow (ofPoly R π q), map_one]; rfl

theorem isUnit_discr : IsUnit ((ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1)) := by
  rw [← ofPoly_edgeDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (edgeQuot.discr R π q)

def point : (chartE R π q).obj (CommAlgCat.of R (chartERing R π q)) :=
  ⟨(ξ R π q, η R π q), ξ_mul_η R π q, isUnit_of_mul_isUnit_left (isUnit_discr R π q),
    isUnit_of_mul_isUnit_right (isUnit_discr R π q)⟩

variable {R π q}

abbrev evalPoly {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    MvPolynomial (Fin 2) R →ₐ[R] B :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then x.1.1 else x.1.2)

@[simp] theorem evalPoly_X_zero {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 0) = x.1.1 := by simp [evalPoly, MvPolynomial.aeval_X]

@[simp] theorem evalPoly_X_one {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 1) = x.1.2 := by simp [evalPoly, MvPolynomial.aeval_X]

theorem evalPoly_edgeRel {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    evalPoly x (edgeRel R π) = 0 := by
  have hC : evalPoly x (MvPolynomial.C π) = algebraMap R B π := (evalPoly x).commutes π
  change evalPoly x (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = 0
  rw [map_sub (evalPoly x), map_mul (evalPoly x), evalPoly_X_zero, evalPoly_X_one, hC, x.2.1,
    sub_self]

def evalQuot {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) : edgeQuot R π →ₐ[R] B :=
  Ideal.Quotient.liftₐ (Ideal.span {edgeRel R π}) (evalPoly x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul (evalPoly x), evalPoly_edgeRel, mul_zero])

theorem evalQuot_mk {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B)
    (p : MvPolynomial (Fin 2) R) : evalQuot x (edgeQuot.mk R π p) = evalPoly x p := rfl

theorem isUnit_evalQuot_of_mem_powers {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B)
    (y : Submonoid.powers (edgeQuot.discr R π q)) :
    IsUnit (evalQuot x (y : edgeQuot R π)) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  rw [edgeQuot.discr, evalQuot_mk]
  change IsUnit (evalPoly x ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)))
  rw [map_mul (evalPoly x), map_sub (evalPoly x), map_sub (evalPoly x), map_pow (evalPoly x),
    map_pow (evalPoly x),
    map_one, evalPoly_X_zero, evalPoly_X_one]
  exact x.2.2.1.mul x.2.2.2

def lift {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) : chartERing R π q →ₐ[R] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (edgeQuot.discr R π q))
    (f := evalQuot x) (isUnit_evalQuot_of_mem_powers x)

theorem lift_ofPoly {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B)
    (p : MvPolynomial (Fin 2) R) : lift x (ofPoly R π q p) = evalPoly x p := by
  rw [lift, IsLocalization.liftAlgHom_apply, ofPoly, AlgHom.comp_apply]
  exact (IsLocalization.lift_eq _ _).trans (evalQuot_mk x p)

@[simp] theorem lift_ξ {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    lift x (ξ R π q) = x.1.1 := by
  rw [ξ, lift_ofPoly, evalPoly_X_zero]

@[simp] theorem lift_η {B : CommAlgCat.{0} R} (x : (chartE R π q).obj B) :
    lift x (η R π q) = x.1.2 := by
  rw [η, lift_ofPoly, evalPoly_X_one]

variable (R π q) in
def corepEquiv (B : CommAlgCat.{0} R) : (chartERing R π q →ₐ[R] B) ≃ (chartE R π q).obj B where
  toFun φ := (chartE R π q).map (CommAlgCat.ofHom φ) (point R π q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (edgeQuot.discr R π q))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change lift ((chartE R π q).map (CommAlgCat.ofHom φ) (point R π q))
      (ofPoly R π q (MvPolynomial.X i)) = φ (ofPoly R π q (MvPolynomial.X i))
    fin_cases i
    · exact lift_ξ _
    · exact lift_η _
  right_inv x := Subtype.ext (Prod.ext (lift_ξ x) (lift_η x))

@[simp] theorem corepEquiv_apply_val (B : CommAlgCat.{0} R) (φ : chartERing R π q →ₐ[R] B) :
    (corepEquiv R π q B φ).1 = (φ (ξ R π q), φ (η R π q)) := rfl

theorem corepEquiv_natural {B B' : CommAlgCat.{0} R} (f : B ⟶ B')
    (φ : chartERing R π q →ₐ[R] B) :
    corepEquiv R π q B' (f.hom.comp φ) = (chartE R π q).map f (corepEquiv R π q B φ) :=
  Subtype.ext rfl

variable (R π q) in
def corepresentableBy :
    (chartE R π q).CorepresentableBy (CommAlgCat.of R (chartERing R π q)) where
  homEquiv {B} := CategoryTheory.ConcreteCategory.homEquiv.trans (corepEquiv R π q B)
  homEquiv_comp g f := by exact corepEquiv_natural g f.hom

variable (R π q) in
def corepIso :
    CategoryTheory.coyoneda.obj (Opposite.op (CommAlgCat.of R (chartERing R π q))) ≅
      chartE R π q :=
  (corepresentableBy R π q).toIso

theorem corepIso_hom_app_val (B : CommAlgCat.{0} R)
    (φ : CommAlgCat.of R (chartERing R π q) ⟶ B) :
    ((corepIso R π q).hom.app B φ).1 = (φ.hom (ξ R π q), φ.hom (η R π q)) := rfl

theorem corepIso_inv_app (B : CommAlgCat.{0} R) (x : (chartE R π q).obj B) :
    (corepIso R π q).inv.app B x = CommAlgCat.ofHom (lift x) := rfl

end chartERing

section Level

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q n : ℕ)

abbrev truncRing : Type := 𝒪 ⧸ Ideal.span {π ^ (n + 1)}

abbrev chartVRingMod : Type := chartVRing (truncRing 𝒪 π n) q

abbrev chartERingMod : Type :=
  chartERing (truncRing 𝒪 π n) (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) π) q

theorem isNilpotent_algebraMap_of_isScalarTower (B : Type) [CommRing B] [Algebra 𝒪 B]
    [Algebra (truncRing 𝒪 π n) B] [IsScalarTower 𝒪 (truncRing 𝒪 π n) B] : IsNilpotent (algebraMap 𝒪
      B π) := by
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (truncRing 𝒪 π n) B,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span
      (Set.mem_singleton _)),
    map_zero]

end Level

end ChartRings

end FormalOmega
end CerednikDrinfeld

end

namespace CerednikDrinfeld
namespace FormalOmega

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)

abbrev OmegaNrObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type :=
  (Onr →ₐ[𝒪] B) × OmegaObj (K := K) π B

def OmegaNr.IsTwistedAct (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin
  2) K)
    (x x' : OmegaNrObj (K := K) π Onr B) : Prop :=
  x'.1 = frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1 ∧
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ x.2 x'.2

end OmegaNr

end FormalOmega
end CerednikDrinfeld
