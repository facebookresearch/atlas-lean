/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_SpecialFormalModule.lean`,
`Definitions/Def_AlgebraicGeometry_FormalGroupAlongSection.lean`,
`Definitions/Def_CerednikDrinfeld_QMFormalCompletionAlong.lean` and
`Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.Frobenius
public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor
public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurve

/-!
# Formal coordinates and formal completion of QM moduli

Formal coordinates for a relative group law along its identity section,
and the formal-completion and formal-module predicates for fake elliptic
curves at a ramified prime.

Formal `O_D`-modules (`CerednikDrinfeld.FormalODModule`) come from
`MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor`: a
two-dimensional commutative formal group with an action of the Witt
vectors `W(𝔽_{p²})`, the ring of integers of the unramified quadratic
extension of `ℚ_p`, and an endomorphism `ϖ` squaring to the action of `p`
and twisted by Frobenius; together they give an action of the ring of
integers `O_D` of the quaternion division algebra over `ℚ_p`. That
structure is only the carrier of the `O_D`-action: the specialness and
height conditions are added by `SpecialFormalODModule`, and, as in the
source, `IsFormalModuleOf` takes a plain `FormalODModule`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPowerSeries

open scoped Quaternion

universe u

namespace MvFormalGroup

variable {B : Type u} [CommRing B]

/-- Evaluation of a power series at a nilpotent point, truncated at
order `n`. -/
def nilEval {σ : Type*} [Fintype σ] [DecidableEq σ] {B' : Type*} [CommRing B']
    [Algebra B B'] (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') : B' :=
  MvPolynomial.aeval a
    (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ)

/-- Multiplication of nilpotent points for a formal group. -/
def nilMul {g : ℕ} (F : MvFormalGroup g B) {B' : Type*} [CommRing B']
    [Algebra B B'] (n : ℕ) (s t : Fin g → B') : Fin g → B' :=
  fun i => nilEval n (F.toPowerSeries i) (Sum.elim s t)

end MvFormalGroup

namespace AlgebraicGeometry.RelativeGroupLaw

variable {B : Type u} [CommRing B] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of B)}

/-- Coordinates for the formal group of a relative group law along its
identity section. -/
abbrev FormalCoordinates (f : A ⟶ Spec (CommRingCat.of B)) (g : ℕ) :
    Type (u + 1) :=
  ∀ (B' : Type u) [CommRing B'] [Algebra B B'], (Fin g → B') →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B B'))) f

/-- A point with values in `B'` is infinitesimal along an ideal `J` of
`B'` if its reduction modulo `J` is the identity point. -/
def IsInfinitesimal (L : RelativeGroupLaw B f) {B' : Type u} [CommRing B']
    [Algebra B B'] (J : Ideal B')
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B B'))) f) :
    Prop :=
  CerednikDrinfeld.QM.compPt
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
          AlgHom.comp_algebraMap]) P =
    L.one (Spec.map (CommRingCat.ofHom (algebraMap B (B' ⧸ J))))

/-- Coordinates are formal coordinates for a formal group if they are
natural in the nilpotent point and if, on each ideal `J` with
`J ^ (n + 1) = ⊥`, they map the points with coordinates in `J`
bijectively onto the points infinitesimal along `J` and carry the
truncated formal group law to the group law. -/
def IsFormalCoordinates (L : RelativeGroupLaw B f) {g : ℕ}
    (F : MvFormalGroup g B) (θ : FormalCoordinates f g) : Prop :=
  (∀ (B' : Type u) [CommRing B'] [Algebra B B'] (B'' : Type u) [CommRing B'']
      [Algebra B B''] (φ : B' →ₐ[B] B'') (s : Fin g → B'),
      (∀ i, IsNilpotent (s i)) →
      θ B'' (φ ∘ s) = CerednikDrinfeld.QM.compPt
        (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
          ext x
          exact φ.commutes x) (θ B' s)) ∧
  (∀ (B' : Type u) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
      J ^ (n + 1) = ⊥ →
      (∀ s : Fin g → B', (∀ i, s i ∈ J) → L.IsInfinitesimal J (θ B' s)) ∧
      (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) →
        θ B' s = θ B' t → s = t) ∧
      (∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B B'))) f,
        L.IsInfinitesimal J P → ∃ s : Fin g → B', (∀ i, s i ∈ J) ∧ θ B' s = P) ∧
      (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) →
        θ B' (F.nilMul n s t) =
          L.mul (Spec.map (CommRingCat.ofHom (algebraMap B B'))) (θ B' s)
            (θ B' t)))

/-- A relative group law has a formal group along its identity section
if it has formal coordinates for some formal group. -/
def IsFormalGroupAlong (L : RelativeGroupLaw B f) {g : ℕ}
    (F : MvFormalGroup g B) : Prop :=
  ∃ θ : FormalCoordinates f g, L.IsFormalCoordinates F θ

end AlgebraicGeometry.RelativeGroupLaw

namespace CerednikDrinfeld.QM

/-- A coordinate on the order `Λ` is an order coordinate at `q` if it is
additive, unital, multiplicative with Frobenius-twisted second
component, injective, dense modulo powers of `q`, and compatible with
the quaternion trace. -/
structure IsOrderCoord {a b : ℚ} (Λ : Subring ℍ[ℚ, a, b]) (q : ℕ)
    [Fact q.Prime] (coord : ↥Λ → Zp2 q × Zp2 q) : Prop where
  /-- The coordinate is additive. -/
  map_add : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m'
  /-- The coordinate sends `1` to `(1, 0)`. -/
  map_one : coord 1 = (1, 0)
  /-- The coordinate is multiplicative with Frobenius twist. -/
  map_mul : ∀ m m' : ↥Λ,
    coord (m * m') =
      ((coord m).1 * (coord m').1 +
        (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m').2),
        (coord m).1 * (coord m').2 +
          (coord m).2 * WittVector.frobenius (coord m').1)
  /-- The coordinate is injective. -/
  injective : Function.Injective coord
  /-- The image of the coordinate is dense. -/
  dense : ∀ (k : ℕ) (α β : Zp2 q), ∃ m : ↥Λ,
    (coord m).1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧
      (coord m).2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k}
  /-- The coordinate is compatible with the trace. -/
  trace : ∀ (m : ↥Λ) (n : ℤ),
    (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
    (coord m).1 + WittVector.frobenius (coord m).1 = (n : Zp2 q)

/-- Formal completion of QM moduli along a fibre: the formal
coordinates on the second moduli problem, evaluated through series
`φ`, agree with the map of points induced by the morphism of moduli
problems. -/
def IsFormalCompletionAlong {B : Type u} [CommRing B] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}
    {g g' : ℕ}
    (θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates f g)
    (θ' : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates f' g')
    (h : A ⟶ A') (hh : h ≫ f' = f) (φ : Fin g' → MvPowerSeries (Fin g) B) :
    Prop :=
  ∀ (B' : Type u) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
    J ^ (n + 1) = ⊥ → ∀ s : Fin g → B', (∀ i, s i ∈ J) →
      θ' B' (fun i => MvFormalGroup.nilEval n (φ i) s) =
        mapPt h hh (θ B' s)

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
  {B : Type u} [CommRing B]

/-- A fake elliptic curve is a formal module over `X` via coordinates
`θ` if `θ` is a formal coordinate system for `X` and the order action
on points is given by the series action of the coordinate. -/
def IsFormalModuleVia (E : FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2) :
    Prop :=
  E.L.IsFormalCoordinates X.F θ ∧
  (∀ (B' : Type u) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
    J ^ (n + 1) = ⊥ → ∀ (m : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
      θ B' (fun i => MvFormalGroup.nilEval n
          (CerednikDrinfeld.SpecialFormal.Series.addVia X.F (X.act (coord m).1)
            ((X.act (coord m).2).comp X.varpi) i) s) =
        pushPt (E.act m) (E.act_over m) (θ B' s))

/-- A fake elliptic curve is a formal module over `X` if it is one via
some formal coordinates. -/
def IsFormalModuleOf (E : FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B) : Prop :=
  ∃ θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2,
    E.IsFormalModuleVia coord X θ

theorem isFormalModuleOf_iff (E : FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B) :
    E.IsFormalModuleOf coord X ↔
      ∃ θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2,
        E.IsFormalModuleVia coord X θ :=
  Iff.rfl

end FakeEllipticCurve

end CerednikDrinfeld.QM
