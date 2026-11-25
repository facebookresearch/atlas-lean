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
public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurve
public import MathlibExt.RingTheory.MvFormalGroup

/-!
# Formal `O_D`-modules and formal completion of QM moduli

A formal `O_D`-module here is a two-dimensional commutative formal group
with an action of the Witt vectors `W(𝔽_{p²})`, the ring of integers of
the unramified quadratic extension of `ℚ_p`, and a distinguished
endomorphism `ϖ` squaring to the action of `p` and twisted by Frobenius;
together they give an action of the ring of integers `O_D` of the
quaternion division algebra over `ℚ_p`. As in the
source, this is only the carrier of the `O_D`-action: the specialness
condition on the Lie algebra and the height condition of a special
formal `O_D`-module are not imposed. The formal group of a fake elliptic
curve at a ramified prime carries such a module; this file defines the
module, its homomorphisms and kernel-degree invariant, and the
formal-completion and formal-module predicates for fake elliptic curves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPowerSeries

open scoped Quaternion

universe u v

namespace MvFormalGroup

variable {B : Type} [CommRing B]

/-- Evaluation of a power series at a nilpotent point, truncated at
order `n`. -/
def nilEval {σ : Type} [Fintype σ] [DecidableEq σ] {B' : Type} [CommRing B']
    [Algebra B B'] (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') : B' :=
  MvPolynomial.aeval a
    (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ)

/-- Multiplication of nilpotent points for a formal group. -/
def nilMul {g : ℕ} (F : MvFormalGroup g B) {B' : Type} [CommRing B']
    [Algebra B B'] (n : ℕ) (s t : Fin g → B') : Fin g → B' :=
  fun i => nilEval n (F.toPowerSeries i) (Sum.elim s t)

end MvFormalGroup

namespace AlgebraicGeometry.RelativeGroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

/-- Coordinates for the formal group of a relative group law along its
identity section. -/
abbrev FormalCoordinates (f : A ⟶ Spec (CommRingCat.of B)) (g : ℕ) : Type 1 :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'], (Fin g → B') →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B B'))) f

/-- A point with values in `B'` is infinitesimal along an ideal `J` of
`B'` if its reduction modulo `J` is the identity point. -/
def IsInfinitesimal (L : RelativeGroupLaw B f) {B' : Type} [CommRing B']
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
  (∀ (B' : Type) [CommRing B'] [Algebra B B'] (B'' : Type) [CommRing B'']
      [Algebra B B''] (φ : B' →ₐ[B] B'') (s : Fin g → B'),
      (∀ i, IsNilpotent (s i)) →
      θ B'' (φ ∘ s) = CerednikDrinfeld.QM.compPt
        (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
          ext x
          exact φ.commutes x) (θ B' s)) ∧
  (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
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

namespace CerednikDrinfeld

/-- The Witt vectors over the field with `p ^ 2` elements: the ring of
integers of the unramified quadratic extension of `ℚ_p`. The ring of
integers of the quaternion division algebra over `ℚ_p` is generated over
it by an element `varpi` as in `FormalODModule`. -/
abbrev Zp2 (p : ℕ) [Fact p.Prime] : Type := WittVector p (GaloisField p 2)

namespace SpecialFormal

variable {p : ℕ} [Fact p.Prime]
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

/-- Two-variable power series over `B`. -/
abbrev Series (B : Type u) [CommRing B] : Type u := Fin 2 → MvPowerSeries (Fin 2) B

/-- The identity series. -/
def Series.id (B : Type u) [CommRing B] : Series B := fun i => MvPowerSeries.X i

/-- Composition of series. -/
def Series.comp (ψ φ : Series B) : Series B := fun i => subst φ (ψ i)

/-- Addition of points defined by series, via a formal group. -/
def Series.addVia (F : MvFormalGroup 2 B) (φ ψ : Series B) : Series B :=
  fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i)

/-- Base change of a series. -/
def Series.map (f : B →+* B') (φ : Series B) : Series B' :=
  fun i => MvPowerSeries.map f (φ i)

/-- A series is a homomorphism of formal groups. -/
def IsLawHom (F G : MvFormalGroup 2 B) (φ : Series B) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧
  ∀ i, subst F.toPowerSeries (φ i) =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) :
            MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) :
            MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      (G.toPowerSeries i)

namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}

/-- A law homomorphism as a formal-group homomorphism. -/
def toHom (h : IsLawHom F G φ) : MvFormalGroup.Hom F G := ⟨φ, h.1, h.2⟩

@[simp]
theorem toHom_toPowerSeries (h : IsLawHom F G φ) :
    h.toHom.toPowerSeries = φ := rfl

/-- A formal-group homomorphism is a law homomorphism. -/
theorem of_hom (f : MvFormalGroup.Hom F G) : IsLawHom F G f.toPowerSeries :=
  ⟨f.constantCoeff_eq_zero, f.subst_eq⟩

/-- A law homomorphism can be substituted. -/
theorem hasSubst (h : IsLawHom F G φ) : HasSubst φ :=
  hasSubst_of_constantCoeff_zero h.1

/-- The identity is a law homomorphism. -/
theorem id (F : MvFormalGroup 2 B) : IsLawHom F F (Series.id B) :=
  of_hom (MvFormalGroup.Hom.id F)

/-- Law homomorphisms compose. -/
theorem comp (hψ : IsLawHom G H ψ) (hφ : IsLawHom F G φ) :
    IsLawHom F H (ψ.comp φ) :=
  of_hom (hψ.toHom.comp hφ.toHom)

end IsLawHom

theorem Series.constantCoeff_comp {ψ φ : Series B}
    (hψ : ∀ i, constantCoeff (ψ i) = 0) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (i : Fin 2) : constantCoeff ((ψ.comp φ) i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hφ) hφ (hψ i)

end SpecialFormal

open SpecialFormal

/-- A formal `O_D`-module: a two-dimensional commutative formal group
with an action of `Zp2 p` by law homomorphisms and a distinguished
endomorphism `varpi` with `varpi² = act p` and Frobenius-twisted
commutation with the action. This is only the `O_D`-action carrier: it
imposes neither the specialness condition on the Lie algebra nor a
height condition. -/
structure FormalODModule (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] where
  /-- The underlying formal group. -/
  F : MvFormalGroup 2 B
  /-- The formal group is commutative. -/
  isComm : F.IsComm
  /-- The action of `Zp2 p`. -/
  act : Zp2 p → Series B
  /-- The distinguished endomorphism. -/
  varpi : Series B
  /-- The action is by law homomorphisms. -/
  isLawHom_act : ∀ a, IsLawHom F F (act a)
  /-- `varpi` is a law homomorphism. -/
  isLawHom_varpi : IsLawHom F F varpi
  /-- The element `1` acts as the identity. -/
  act_one : act 1 = Series.id B
  /-- The action is multiplicative. -/
  act_mul : ∀ a b, act (a * b) = (act a).comp (act b)
  /-- The action is additive on points. -/
  act_add : ∀ a b, act (a + b) = Series.addVia F (act a) (act b)
  /-- `varpi` composed with itself is the action of `p`. -/
  varpi_comp_varpi : varpi.comp varpi = act (p : Zp2 p)
  /-- `varpi` commutes with the action up to Frobenius. -/
  varpi_comp_act : ∀ a, varpi.comp (act a) =
    (act (WittVector.frobenius a)).comp varpi

namespace FormalODModule

variable {p : ℕ} [Fact p.Prime]
variable {B : Type u} [CommRing B]

theorem ext' {X Y : FormalODModule p B} (hF : X.F = Y.F) (ha : X.act = Y.act)
    (hv : X.varpi = Y.varpi) : X = Y := by
  cases X; cases Y; cases hF; cases ha; cases hv; rfl

/-- A series is a homomorphism of formal `O_D`-modules if it is a law
homomorphism commuting with the action and with `varpi`. -/
def IsODHom (X Y : FormalODModule p B) (φ : Series B) : Prop :=
  IsLawHom X.F Y.F φ ∧ (∀ a, φ.comp (X.act a) = (Y.act a).comp φ) ∧
    φ.comp X.varpi = Y.varpi.comp φ

/-- The kernel algebra of a series. -/
abbrev KerAlgebra (φ : Series B) : Type u :=
  MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range φ)

/-- A series has kernel of degree `d` if its kernel algebra is finite
projective and has rank `d` over every field-valued point. -/
def HasKernelOfDegree (φ : Series B) (d : ℕ) : Prop :=
  Module.Finite B (KerAlgebra φ) ∧ Module.Projective B (KerAlgebra φ) ∧
    ∀ (κ : Type u) [Field κ] (f : B →+* κ),
      Module.finrank κ (KerAlgebra (φ.map f)) = d

/-- A series is an isogeny of height `h` between formal modules: a
homomorphism of formal `O_D`-modules whose kernel has degree `p ^ h`. -/
def IsIsogenyOfHeight (X Y : FormalODModule p B) (φ : Series B) (h : ℕ) :
    Prop :=
  IsODHom X Y φ ∧ HasKernelOfDegree φ (p ^ h)

/-- The height of a formal module is measured by the action of `p`. -/
def HasHeight (X : FormalODModule p B) (h : ℕ) : Prop :=
  HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h)

end FormalODModule

end CerednikDrinfeld

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
def IsFormalCompletionAlong {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}
    {g g' : ℕ}
    (θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates f g)
    (θ' : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates f' g')
    (h : A ⟶ A') (hh : h ≫ f' = f) (φ : Fin g' → MvPowerSeries (Fin g) B) :
    Prop :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
    J ^ (n + 1) = ⊥ → ∀ s : Fin g → B', (∀ i, s i ∈ J) →
      θ' B' (fun i => MvFormalGroup.nilEval n (φ i) s) =
        mapPt h hh (θ B' s)

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
  {B : Type} [CommRing B]

/-- A fake elliptic curve is a formal module over `X` via coordinates
`θ` if `θ` is a formal coordinate system for `X` and the order action
on points is given by the series action of the coordinate. -/
def IsFormalModuleVia (E : FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2) :
    Prop :=
  E.L.IsFormalCoordinates X.F θ ∧
  (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ),
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
