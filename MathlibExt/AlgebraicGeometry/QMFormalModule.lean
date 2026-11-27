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
# Formal coordinates and formal-module conditions for QM moduli

Formal coordinates for a relative group law along its identity section,
and, for fake elliptic curves at a ramified prime, the formal-module
predicates and `IsFormalCompletionAlong`, the compatibility condition
the source states for the formal completion of QM moduli along a fibre.
Power series are evaluated with `MvFormalGroup.nilEval`, which bounds
each exponent by `n`; every use of it here is at points with coordinates
in an ideal `J` with `J ^ (n + 1) = ⊥`, where it agrees with truncation at
total degree `n`.

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

/-- Evaluation of a power series `φ` at a point `a`, after truncating `φ`
to the monomials whose exponent in each variable is at most `n`
(`MvPowerSeries.trunc'` at the constant bound `n`), not to the monomials
of total degree at most `n`. The point `a` is arbitrary. When every `a i`
lies in an ideal `J` with `J ^ (n + 1) = ⊥`, every monomial of total
degree above `n` vanishes at `a`, so the two truncations give the same
value. -/
def nilEval {σ : Type*} [Fintype σ] [DecidableEq σ] {B' : Type*} [CommRing B']
    [Algebra B B'] (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') : B' :=
  MvPolynomial.aeval a
    (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ)

/-- The formal group law of `F` evaluated with `nilEval n` at a pair of
points `s` and `t`. The points are arbitrary; when their coordinates lie
in an ideal `J` with `J ^ (n + 1) = ⊥`, this is the product of `s` and `t`
under `F`. -/
def nilMul {g : ℕ} (F : MvFormalGroup g B) {B' : Type*} [CommRing B']
    [Algebra B B'] (n : ℕ) (s t : Fin g → B') : Fin g → B' :=
  fun i => nilEval n (F.toPowerSeries i) (Sum.elim s t)

end MvFormalGroup

namespace AlgebraicGeometry.RelativeGroupLaw

variable {B : Type u} [CommRing B] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of B)}

/-- A coordinate family: for each `B`-algebra `B'` in the universe of `B`,
a map from `g`-tuples in `B'` to the `B'`-points of `A` over `Spec B`.
No condition is imposed; `IsFormalCoordinates` says when such a family
is a system of formal coordinates for a formal group. -/
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

/-- A coordinate family `θ` is a system of formal coordinates for the
formal group `F` if it is natural in `B'` at points with nilpotent
coordinates and if, for each ideal `J` with `J ^ (n + 1) = ⊥`, it maps the
points with coordinates in `J` bijectively onto the points infinitesimal
along `J` and carries the law `F.nilMul n` on those points to the group
law. -/
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

/-- A relative group law has the formal group `F` along its identity
section if some coordinate family is a system of formal coordinates for
`F`. -/
def IsFormalGroupAlong (L : RelativeGroupLaw B f) {g : ℕ}
    (F : MvFormalGroup g B) : Prop :=
  ∃ θ : FormalCoordinates f g, L.IsFormalCoordinates F θ

end AlgebraicGeometry.RelativeGroupLaw

namespace CerednikDrinfeld.QM

/-- A map `coord` from a subring `Λ` of `ℍ[ℚ, a, b]` to `Zp2 q × Zp2 q` is
an order coordinate at `q` if it is additive, sends `1` to `(1, 0)`, is
multiplicative for the product
`(x₁, x₂) * (y₁, y₂) = (x₁ y₁ + q x₂ σ(y₂), x₁ y₂ + x₂ σ(y₁))`, with `σ`
the Frobenius, is injective, has image meeting every class modulo `q ^ k`
for every `k`, and sends each element whose reduced trace is an integer
`n` to a pair whose first entry `x` satisfies `x + σ(x) = n`. -/
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

/-- Compatibility of coordinate families `θ` on `A` and `θ'` on `A'` with a
morphism `h : A ⟶ A'` over `Spec B`, through the power series `φ`: for
every `B`-algebra `B'`, ideal `J` of `B'` with `J ^ (n + 1) = ⊥` and point
`s` with coordinates in `J`, the point `θ' B' (fun i => nilEval n (φ i) s)`
is the image under `h` of `θ B' s`. It does not require `θ` or `θ'` to be
formal coordinate systems, and it does not assert that `h` represents or
identifies a formal completion; the name follows the source. -/
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

/-- A fake elliptic curve `E` is a formal module over `X` via a coordinate
family `θ` if `θ` is a system of formal coordinates for the formal group
of `X` and the action of `Λ` matches that of `O_D` on `X` at points with
coordinates in an ideal `J` with `J ^ (n + 1) = ⊥`: for `m : Λ` with
`coord m = (c₁, c₂)`, `θ` sends the value under `nilEval n` of the series
of `c₁ + c₂ ϖ` (the sum, for the law of `X`, of `X.act c₁` and of
`X.act c₂` after `ϖ`) at such a point `s` to the image of `θ B' s` under
`E.act m`. -/
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

/-- A fake elliptic curve `E` is a formal module over `X` if it is one via
some coordinate family, in the sense of `IsFormalModuleVia`. -/
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
