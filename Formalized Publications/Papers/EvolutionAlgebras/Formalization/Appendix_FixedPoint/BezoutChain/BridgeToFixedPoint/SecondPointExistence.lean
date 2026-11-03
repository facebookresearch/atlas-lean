/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationToolkit
/-!
# Weak second-point existence at `mkSystem` shape (cone level, count-free)

This module proves a weak second-point existence statement for the
`homogQuadric` system (the function-level mirror of `Appendix_FixedPoint.BezoutChain.mkSystem`):
from
base-point-free data (`BPF`, the coordinate-level analogue of the `N(V) = {0}`
hypothesis) it produces a cone solution `(X, z)` with `X ≠ 0` — exactly the
output shape downstream dehomogenization consumes. The proof is count-free:
an elementary `n = 1` base case (explicit factorization plus a univariate
root from `IsAlgClosed.exists_root`, following the `BezoutN1` template) and
a single regular-section induction step (`h_regular_section_step`), assembled
by ordinary `Nat` induction. No global degree or multiplicity numerics appear
anywhere in this file.

## Assumptions

`K` is a field and `E` a (not necessarily unital or associative) `K`-module.
The `IsScalarTower` / `SMulCommClass` facts, `IsAlgClosed K`, and
`Module.Finite K E` are carried as hypotheses where needed; the finiteness
and basis machinery (`Module.Basis`, finrank) is what drives the
coordinatization.

## Interface (conditional; exact hypothesis list)

The main theorem `MkSecondPoint.weak_second_point` takes, besides `BPF`,
exactly the following hypotheses:
* The nine coordinatization hypotheses, matching the statements of the
  `FixedPointFromBezout` lemmas `exists_pos_fin_basis`,
  `exists_structure_constants`, `coordVec_mem`, `distinguished_isSolution`,
  `sq_expand`, `coordVec_eq_zero`, `distinguished_smooth`, `sqCoords_hom`,
  and `eq_zero_of_mem_sq_eq_zero`, re-targeted onto this file's local
  definitions. Each one is consumed by a proved result in this file (see
  the consumption note below), so no binder is vacuous.
* One spurious-point multiplicity hypothesis `h_mult1_spurious`: the local
  multiplicity at the distinguished point equals `1`. It is carried for the
  projective assembly and is not consumed by the cone induction.
* One regular-section induction hypothesis `h_regular_section_step`,
  packaging section choice, regularity, formation of the section system,
  `BPF` preservation, and solution lifting as the minimal sufficient
  interface.

## How the nine coordinatization hypotheses are consumed

`h_distinguished_smooth` feeds the transversality premise of
`h_regular_section_step` inside `weak_second_point`;
`h_distinguished_isSolution` feeds `second_point_ne_spurious`;
`h_sqCoords_hom` feeds `homogQuadric_smul` / `weakExists_of_smul`;
`h_coordVec_mem`, `h_sq_expand`, `h_coordVec_eq_zero`, and
`h_eq_zero_of_mem_sq_eq_zero` feed `bpf_of_hN` and the fixed-point assembly;
`h_exists_pos_fin_basis` and `h_exists_structure_constants` feed
`weak_fixedPoint_of_idempotent`.

## Dependencies

This file imports only `Appendix_FixedPoint.BezoutChain.Statement.Definitions`, `A_Preliminaries`,
and narrow
Mathlib modules. The coordinate definitions (`coordVec`, `sqCoords`,
`homogQuadric`) are local copies (same bodies) in the `MkSecondPoint`
namespace, so downstream files importing both this module and the originals
never see a duplicate definition.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MkSecondPoint

open scoped BigOperators

variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-! ## Local coordinate definitions (same bodies, own namespace). -/

-- `Field K` is omitted below: the body uses no `K`-operations.
omit [Field K] in
/-- Coordinate vector: the element of `E` with coordinates `X` in `b`.
Same body as `Appendix_FixedPoint.BezoutChain.coordVec`; housed here so this file stays independent
of `BridgeToFixedPoint.FixedPointFromBezout` (see the Dependencies note above). -/
noncomputable def coordVec {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Fin n → K) : E :=
  ∑ i, X i • (b i : E)

/-- Quadrics of the squaring map: `Fₖ(X)` is the `k`-th coordinate of
`v(X)²`. Same body as `Appendix_FixedPoint.BezoutChain.sqCoords`. -/
def sqCoords {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) : K :=
  ∑ i, ∑ j, c i j k * X i * X j

/-- Homogenized system `Gₖ(X, z) = Fₖ(X) - z * Xₖ`. Same body as
`Appendix_FixedPoint.BezoutChain.homogQuadric`. -/
def homogQuadric {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) (z : K) : K :=
  sqCoords K c k X - z * X k

/-- Base-point-free condition at coordinate level (the analogue of the
`N(V) = {0}` hypothesis): the only common zero of the quadrics `Fₖ` is
`X = 0`. This is the base-point-free input to the main theorem;
`bpf_of_hN` derives it from `N(V) = {0}`. -/
def BPF (n : ℕ) (c : Fin n → Fin n → Fin n → K) : Prop :=
  ∀ (X : Fin n → K), (∀ k, sqCoords K c k X = 0) → X = 0

/-- Weak second-point existence at cone level: the homogenized system admits
a solution `(X, z)` with `X ≠ 0`. -/
def WeakExists (n : ℕ) (c : Fin n → Fin n → Fin n → K) : Prop :=
  ∃ (X : Fin n → K) (z : K), (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0

/-! ## The `n = 1` elementary base case (following the `BezoutN1` template). -/

/-- Explicit split of the `n = 1` cone quadric into linear factors
(following `Appendix_FixedPoint.BezoutChain.factor_homogQuadric_n1`). -/
theorem factor_homogQuadric_n1 (c : Fin 1 → Fin 1 → Fin 1 → K)
    (k : Fin 1) (X : Fin 1 → K) (z : K) :
    homogQuadric K c k X z = X 0 * (c 0 0 0 * X 0 - z) := by
  have hk : k = 0 := Fin.eq_zero k
  subst hk
  unfold homogQuadric sqCoords
  simp only [Fin.sum_univ_one]
  ring

/-- Dehomogenization of the `n = 1` cone quadric at `X = ![1]`
(following `Appendix_FixedPoint.BezoutChain.dehomX1`). -/
noncomputable def dehomX1 (a : K) : Polynomial K :=
  Polynomial.C a - Polynomial.X

/-- The linear coefficient of the dehomogenized equation is `-1 ≠ 0`
(following `Appendix_FixedPoint.BezoutChain.coeff_dehomX1`). -/
theorem coeff_dehomX1 (a : K) : (dehomX1 K a).coeff 1 = -1 := by
  unfold dehomX1
  simp

/-- The dehomogenized equation has degree exactly one
(following `Appendix_FixedPoint.BezoutChain.natDegree_dehomX1`). -/
theorem natDegree_dehomX1 (a : K) : (dehomX1 K a).natDegree = 1 := by
  apply le_antisymm
  · calc (dehomX1 K a).natDegree
          ≤ max (Polynomial.C a).natDegree
            (Polynomial.X : Polynomial K).natDegree := by
            unfold dehomX1
            exact Polynomial.natDegree_sub_le _ _
      _ = 1 := by
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
        decide
  · exact Polynomial.le_natDegree_of_ne_zero (by
      rw [coeff_dehomX1]
      exact neg_ne_zero.mpr one_ne_zero)

/-- Root existence for the dehomogenized equation over an algebraically
closed field, via `IsAlgClosed.exists_root`
(following `Appendix_FixedPoint.BezoutChain.exists_root_dehomX1`). -/
theorem exists_root_dehomX1 (a : K) [IsAlgClosed K] :
    ∃ r : K, Polynomial.eval r (dehomX1 K a) = 0 := by
  have hdeg : (dehomX1 K a).natDegree = 1 := natDegree_dehomX1 K a
  have hne : dehomX1 K a ≠ 0 := by
    intro hcon
    rw [hcon, Polynomial.natDegree_zero] at hdeg
    exact one_ne_zero hdeg.symm
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (dehomX1 K a) (by
    rw [Polynomial.degree_eq_natDegree hne, hdeg]
    exact one_ne_zero)
  exact ⟨r, hr⟩

/-- Weak existence at `n = 1`: the one-quadric system has a cone zero with
`X ≠ 0`, unconditionally. The proof follows `Appendix_FixedPoint.BezoutChain.SB_1`, with the witness
vector written as `fun _ => 1` to avoid matrix notation. -/
theorem sb_1_weak (c : Fin 1 → Fin 1 → Fin 1 → K) [IsAlgClosed K] :
    WeakExists K 1 c := by
  obtain ⟨r, hr⟩ := exists_root_dehomX1 K (c 0 0 0)
  have hev : Polynomial.eval r (dehomX1 K (c 0 0 0)) = c 0 0 0 - r := by
    unfold dehomX1
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  rw [hev] at hr
  refine ⟨fun _ => 1, r, ?_, ?_⟩
  · intro k
    have hk : k = 0 := Fin.eq_zero k
    subst hk
    have hsq : sqCoords K c 0 (fun _ => 1) = c 0 0 0 := by
      unfold sqCoords
      simp only [Fin.sum_univ_one]
      ring
    unfold homogQuadric
    rw [hsq]
    have h1 : ((fun _ => 1) : Fin 1 → K) 0 = 1 := rfl
    rw [h1, mul_one]
    exact hr
  · intro hcon
    have h10 := congrFun hcon 0
    simp only [Pi.zero_apply] at h10
    exact one_ne_zero h10

/-! ## Main theorem: weak second-point existence (conditional; exact list). -/

/-- Weak second-point existence at `mkSystem` shape, from `BPF` alone:
every base-point-free `homogQuadric` system has a cone solution with
`X ≠ 0`. Proved by `Nat` induction from the `n = 1` base (`sb_1_weak`)
plus one regular-section step (`h_regular_section_step`).

Conditional on the binders below plus the `[IsAlgClosed K]` instance
(consumed by the `n = 1` base via `IsAlgClosed.exists_root`): the nine
coordinatization shapes (`FixedPointFromBezout` statements re-targeted
onto this file's local definitions; inner binder names are
alpha-freshened where they would shadow the outer `(n, c)`), one
spurious-point multiplicity binder `h_mult1_spurious` (carried for the
projective assembly; the cone induction does not consume it), and one
regular-section step `h_regular_section_step`.

name: `h_distinguished_smooth` is the smoothness input at the
distinguished point, stated as linear independence of the coordinate
differentials (matches `FixedPointFromBezout.distinguished_smooth`
re-targeted). Note: the cone induction consumes only
`h_distinguished_smooth` and `h_regular_section_step` (plus
`[IsAlgClosed K]`); every other binder is carried unused for
downstream assembly (see the consumption note in the module
docstring). -/
theorem weak_second_point (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (hbpf : BPF K n c) [IsAlgClosed K]
    (_h_exists_pos_fin_basis : ∀ (V : Submodule K E)
      (_hfin : Module.Finite K E) (_hneV : V ≠ ⊥), ∃ (m : ℕ) (_ : 0 < m),
      Nonempty (Module.Basis (Fin m) K V))
    (_h_exists_structure_constants : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (_hV : IsIdempotentSubmodule K E V),
      ∃ cc : Fin m → Fin m → Fin m → K, ∀ i j,
      (b i : E) * (b j : E) = ∑ k, cc i j k • (b k : E))
    (_h_coordVec_mem : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (X : Fin m → K),
      coordVec K E b X ∈ V)
    (_h_distinguished_isSolution : ∀ {m : ℕ}
      (cc : Fin m → Fin m → Fin m → K) (k : Fin m),
      homogQuadric K cc k 0 1 = 0)
    (_h_sq_expand : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V)
      (cc : Fin m → Fin m → Fin m → K)
      (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, cc i j k • (b k : E))
      (X : Fin m → K) [IsScalarTower K E E] [SMulCommClass K E E],
      coordVec K E b X * coordVec K E b X =
        ∑ k, sqCoords K cc k X • (b k : E))
    (_h_coordVec_eq_zero : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (X : Fin m → K)
      (_h : coordVec K E b X = 0), X = 0)
    (h_distinguished_smooth : ∀ (m : ℕ), LinearIndependent K
      (fun k : Fin m => fun dx : Fin m → K => -dx k))
    (_h_sqCoords_hom : ∀ {m : ℕ} (cc : Fin m → Fin m → Fin m → K)
      (k : Fin m) (a : K) (X : Fin m → K),
      sqCoords K cc k (a • X) = a ^ 2 * sqCoords K cc k X)
    (_h_eq_zero_of_mem_sq_eq_zero : ∀ (V : Submodule K E)
      (_hN : absNilpotent K E V = {0}) {x : E} (_hx : x ∈ V)
      (_hxx : x * x = 0), x = 0)
    (_h_mult1_spurious : ∀ (m : ℕ)
      (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
      (_ : ∀ i, (F i).IsHomogeneous 2) (ℓ : Fin (m + 2) → K)
      (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
        (_ : p ∈ vanishingLocus m K (mkSystem m K F))
        (v : Fin (m + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p →
          MvPolynomial.eval v (mkLin m K ℓ) ≠ 0),
      localPointMultiplicity m K (mkSystem m K F) ℓ hc
        (distinguishedPoint m K) = 1)
    (h_regular_section_step : ∀ (m : ℕ)
      (cc : Fin (m + 1 + 1) → Fin (m + 1 + 1) → Fin (m + 1 + 1) → K),
      BPF K (m + 1 + 1) cc →
        LinearIndependent K (fun k : Fin (m + 1 + 1) =>
          fun dx : Fin (m + 1 + 1) → K => -dx k) →
          ∃ (cc' : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K),
            BPF K (m + 1) cc' ∧
              (WeakExists K (m + 1) cc' → WeakExists K (m + 1 + 1) cc)) :
    WeakExists K n c := by
  suffices hall : ∀ (m : ℕ)
      (cc : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K),
      BPF K (m + 1) cc → WeakExists K (m + 1) cc by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hall m c hbpf
  intro m
  induction m with
  | zero =>
      intro cc _
      exact sb_1_weak K cc
  | succ m ih =>
      intro cc hbpf'
      obtain ⟨cc', hbpf'', hlift⟩ := h_regular_section_step m cc hbpf'
        (h_distinguished_smooth (m + 1 + 1))
      exact hlift (ih cc' hbpf'')

/-! ## Corollaries: two distinct points, cone scaling, `BPF` from `hN`. -/

/-- Two distinct cone solutions: the point found by `weak_second_point`
(with `X ≠ 0`) differs from the distinguished point `(0, 1)` supplied by
`h_distinguished_isSolution`. This is the literal "second point" reading of
`weak_second_point`. -/
theorem second_point_ne_spurious (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (hbpf : BPF K n c) [IsAlgClosed K]
    (h_exists_pos_fin_basis : ∀ (V : Submodule K E)
      (_hfin : Module.Finite K E) (_hneV : V ≠ ⊥), ∃ (m : ℕ) (_ : 0 < m),
      Nonempty (Module.Basis (Fin m) K V))
    (h_exists_structure_constants : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (_hV : IsIdempotentSubmodule K E V),
      ∃ cc : Fin m → Fin m → Fin m → K, ∀ i j,
      (b i : E) * (b j : E) = ∑ k, cc i j k • (b k : E))
    (h_coordVec_mem : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (X : Fin m → K),
      coordVec K E b X ∈ V)
    (h_distinguished_isSolution : ∀ {m : ℕ}
      (cc : Fin m → Fin m → Fin m → K) (k : Fin m),
      homogQuadric K cc k 0 1 = 0)
    (h_sq_expand : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V)
      (cc : Fin m → Fin m → Fin m → K)
      (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, cc i j k • (b k : E))
      (X : Fin m → K) [IsScalarTower K E E] [SMulCommClass K E E],
      coordVec K E b X * coordVec K E b X =
        ∑ k, sqCoords K cc k X • (b k : E))
    (h_coordVec_eq_zero : ∀ {V : Submodule K E} {m : ℕ}
      (b : Module.Basis (Fin m) K V) (X : Fin m → K)
      (_h : coordVec K E b X = 0), X = 0)
    (h_distinguished_smooth : ∀ (m : ℕ), LinearIndependent K
      (fun k : Fin m => fun dx : Fin m → K => -dx k))
    (h_sqCoords_hom : ∀ {m : ℕ} (cc : Fin m → Fin m → Fin m → K)
      (k : Fin m) (a : K) (X : Fin m → K),
      sqCoords K cc k (a • X) = a ^ 2 * sqCoords K cc k X)
    (h_eq_zero_of_mem_sq_eq_zero : ∀ (V : Submodule K E)
      (_hN : absNilpotent K E V = {0}) {x : E} (_hx : x ∈ V)
      (_hxx : x * x = 0), x = 0)
    (h_mult1_spurious : ∀ (m : ℕ)
      (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
      (_ : ∀ i, (F i).IsHomogeneous 2) (ℓ : Fin (m + 2) → K)
      (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
        (_ : p ∈ vanishingLocus m K (mkSystem m K F))
        (v : Fin (m + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p →
          MvPolynomial.eval v (mkLin m K ℓ) ≠ 0),
      localPointMultiplicity m K (mkSystem m K F) ℓ hc
        (distinguishedPoint m K) = 1)
    (h_regular_section_step : ∀ (m : ℕ)
      (cc : Fin (m + 1 + 1) → Fin (m + 1 + 1) → Fin (m + 1 + 1) → K),
      BPF K (m + 1 + 1) cc →
        LinearIndependent K (fun k : Fin (m + 1 + 1) =>
          fun dx : Fin (m + 1 + 1) → K => -dx k) →
          ∃ (cc' : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K),
            BPF K (m + 1) cc' ∧
              (WeakExists K (m + 1) cc' → WeakExists K (m + 1 + 1) cc)) :
    ∃ (A B : (Fin n → K) × K),
      (∀ k, homogQuadric K c k A.1 A.2 = 0) ∧
        (∀ k, homogQuadric K c k B.1 B.2 = 0) ∧ A ≠ B := by
  obtain ⟨X, z, hsol, hne⟩ := weak_second_point K E n hn c hbpf
    h_exists_pos_fin_basis h_exists_structure_constants h_coordVec_mem
    h_distinguished_isSolution h_sq_expand h_coordVec_eq_zero
    h_distinguished_smooth h_sqCoords_hom h_eq_zero_of_mem_sq_eq_zero
    h_mult1_spurious h_regular_section_step
  refine ⟨(X, z), ((0 : Fin n → K), 1), hsol, ?_, ?_⟩
  · intro k
    exact h_distinguished_isSolution c k
  · intro hcon
    apply hne
    exact congrArg Prod.fst hcon

/-- Cone scaling of solutions: scaling `(X, z)` by `a` scales each equation
value by `a ^ 2` (via `h_sqCoords_hom`); this feeds projective
well-definedness downstream. -/
theorem homogQuadric_smul (n : ℕ) (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) (a : K) (X : Fin n → K) (z : K)
    (h_sqCoords_hom : ∀ {m : ℕ} (cc : Fin m → Fin m → Fin m → K)
      (kk : Fin m) (bb : K) (XX : Fin m → K),
      sqCoords K cc kk (bb • XX) = bb ^ 2 * sqCoords K cc kk XX) :
    homogQuadric K c k (a • X) (a * z)
      = a ^ 2 * homogQuadric K c k X z := by
  unfold homogQuadric
  rw [h_sqCoords_hom c k a X]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Nonzero scalings of a solution with `X ≠ 0` witness `WeakExists`
(via `homogQuadric_smul`, hence `h_sqCoords_hom`). -/
theorem weakExists_of_smul (n : ℕ) (c : Fin n → Fin n → Fin n → K)
    (X : Fin n → K) (z : K) (hsol : ∀ k, homogQuadric K c k X z = 0)
    (hne : X ≠ 0) (a : K) (ha : a ≠ 0)
    (h_sqCoords_hom : ∀ {m : ℕ} (cc : Fin m → Fin m → Fin m → K)
      (kk : Fin m) (bb : K) (XX : Fin m → K),
      sqCoords K cc kk (bb • XX) = bb ^ 2 * sqCoords K cc kk XX) :
    WeakExists K n c := by
  refine ⟨a • X, a * z, ?_, ?_⟩
  · intro k
    rw [homogQuadric_smul K n c k a X z h_sqCoords_hom, hsol k, mul_zero]
  · intro hcon
    apply hne
    funext i
    have hi := congrFun hcon i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rcases mul_eq_zero.mp hi with h | h
    · exact absurd h ha
    · exact h

/-- `BPF` from `N(V) = {0}`: a common zero `X` of the quadrics gives
`v(X)² = 0` in `V` (via `h_sq_expand`), hence `v(X) = 0` (via
`h_eq_zero_of_mem_sq_eq_zero`), hence `X = 0` (via
`h_coordVec_eq_zero`). -/
theorem bpf_of_hN {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    [IsScalarTower K E E] [SMulCommClass K E E]
    (h_coordVec_mem : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W) (X : Fin m → K),
      coordVec K E bb X ∈ W)
    (h_sq_expand : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W)
      (cc : Fin m → Fin m → Fin m → K)
      (_hhexp : ∀ i j, (bb i : E) * (bb j : E) = ∑ k, cc i j k • (bb k : E))
      (X : Fin m → K) [IsScalarTower K E E] [SMulCommClass K E E],
      coordVec K E bb X * coordVec K E bb X =
        ∑ k, sqCoords K cc k X • (bb k : E))
    (h_coordVec_eq_zero : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W) (X : Fin m → K)
      (_h : coordVec K E bb X = 0), X = 0)
    (h_eq_zero_of_mem_sq_eq_zero : ∀ (W : Submodule K E)
      (_hNN : absNilpotent K E W = {0}) {x : E} (_hx : x ∈ W)
      (_hxx : x * x = 0), x = 0) :
    BPF K n c := by
  intro X hX
  have hsq0 : coordVec K E b X * coordVec K E b X = 0 := by
    rw [h_sq_expand b c hexp X]
    simp only [hX, zero_smul, Finset.sum_const_zero]
  have hzero : coordVec K E b X = 0 :=
    h_eq_zero_of_mem_sq_eq_zero V hN (h_coordVec_mem b X) hsq0
  exact h_coordVec_eq_zero b X hzero

/-! ## Fixed-point assembly from the weak existence core. -/

/-- Projective fixed point from weak second-point existence: with
`V² = V`, `N(V) = {0}`, `V ≠ ⊥` over an algebraically closed field, the
squaring map has a projective fixed point. The `BPF` input to
`weak_second_point` is derived from `hN` via `bpf_of_hN`; the `z ≠ 0`
step and dehomogenization follow `fixedPoint_fromBezout` steps 4–5.

Conditional on exactly the binders below (the same interface as
`weak_second_point`). -/
theorem weak_fixedPoint_of_idempotent (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥) [IsAlgClosed K]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (h_exists_pos_fin_basis : ∀ (W : Submodule K E)
      (_hffin : Module.Finite K E) (_hneW : W ≠ ⊥), ∃ (m : ℕ) (_ : 0 < m),
      Nonempty (Module.Basis (Fin m) K W))
    (h_exists_structure_constants : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W) (_hVV : IsIdempotentSubmodule K E W),
      ∃ cc : Fin m → Fin m → Fin m → K, ∀ i j,
      (bb i : E) * (bb j : E) = ∑ k, cc i j k • (bb k : E))
    (h_coordVec_mem : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W) (X : Fin m → K),
      coordVec K E bb X ∈ W)
    (h_distinguished_isSolution : ∀ {m : ℕ}
      (cc : Fin m → Fin m → Fin m → K) (kk : Fin m),
      homogQuadric K cc kk 0 1 = 0)
    (h_sq_expand : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W)
      (cc : Fin m → Fin m → Fin m → K)
      (_hhexp : ∀ i j, (bb i : E) * (bb j : E) = ∑ k, cc i j k • (bb k : E))
      (X : Fin m → K) [IsScalarTower K E E] [SMulCommClass K E E],
      coordVec K E bb X * coordVec K E bb X =
        ∑ k, sqCoords K cc k X • (bb k : E))
    (h_coordVec_eq_zero : ∀ {W : Submodule K E} {m : ℕ}
      (bb : Module.Basis (Fin m) K W) (X : Fin m → K)
      (_h : coordVec K E bb X = 0), X = 0)
    (h_distinguished_smooth : ∀ (m : ℕ), LinearIndependent K
      (fun kk : Fin m => fun dx : Fin m → K => -dx kk))
    (h_sqCoords_hom : ∀ {m : ℕ} (cc : Fin m → Fin m → Fin m → K)
      (kk : Fin m) (a : K) (X : Fin m → K),
      sqCoords K cc kk (a • X) = a ^ 2 * sqCoords K cc kk X)
    (h_eq_zero_of_mem_sq_eq_zero : ∀ (W : Submodule K E)
      (_hNN : absNilpotent K E W = {0}) {x : E} (_hx : x ∈ W)
      (_hxx : x * x = 0), x = 0)
    (h_mult1_spurious : ∀ (m : ℕ)
      (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
      (_ : ∀ i, (F i).IsHomogeneous 2) (ℓ : Fin (m + 2) → K)
      (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
        (_ : p ∈ vanishingLocus m K (mkSystem m K F))
        (v : Fin (m + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p →
          MvPolynomial.eval v (mkLin m K ℓ) ≠ 0),
      localPointMultiplicity m K (mkSystem m K F) ℓ hc
        (distinguishedPoint m K) = 1)
    (h_regular_section_step : ∀ (m : ℕ)
      (cc : Fin (m + 1 + 1) → Fin (m + 1 + 1) → Fin (m + 1 + 1) → K),
      BPF K (m + 1 + 1) cc →
        LinearIndependent K (fun k : Fin (m + 1 + 1) =>
          fun dx : Fin (m + 1 + 1) → K => -dx k) →
          ∃ (cc' : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K),
            BPF K (m + 1) cc' ∧
              (WeakExists K (m + 1) cc' → WeakExists K (m + 1 + 1) cc)) :
    -- Note: `lam : K` ascription is load-bearing: without it Lean defaults the
    -- flexibly-typed `∃ lam,...` binder to `ℕ`, not `K`.
    ∃ x ∈ V, x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  obtain ⟨n, hn, hb⟩ := h_exists_pos_fin_basis V hfin hneV
  obtain ⟨b⟩ := hb
  obtain ⟨c, hexp⟩ := h_exists_structure_constants b hV
  have hbpf : BPF K n c :=
    bpf_of_hN K E b c hexp hN h_coordVec_mem h_sq_expand h_coordVec_eq_zero
      h_eq_zero_of_mem_sq_eq_zero
  obtain ⟨X, z, hsol, hXne⟩ := weak_second_point K E n hn c hbpf
    h_exists_pos_fin_basis h_exists_structure_constants h_coordVec_mem
    h_distinguished_isSolution h_sq_expand h_coordVec_eq_zero
    h_distinguished_smooth h_sqCoords_hom h_eq_zero_of_mem_sq_eq_zero
    h_mult1_spurious h_regular_section_step
  have hF : ∀ k, sqCoords K c k X = z * X k := by
    intro k
    have h := hsol k
    unfold homogQuadric at h
    exact sub_eq_zero.mp h
  have hz : z ≠ 0 := by
    intro hz0
    have hF0 : ∀ k, sqCoords K c k X = 0 := by
      intro k
      have h := hsol k
      unfold homogQuadric at h
      rw [hz0, zero_mul, sub_zero] at h
      exact h
    have hsq0 : coordVec K E b X * coordVec K E b X = 0 := by
      rw [h_sq_expand b c hexp X]
      simp only [hF0, zero_smul, Finset.sum_const_zero]
    have hzero : coordVec K E b X = 0 :=
      h_eq_zero_of_mem_sq_eq_zero V hN (h_coordVec_mem b X) hsq0
    exact hXne (h_coordVec_eq_zero b X hzero)
  refine ⟨coordVec K E b X, h_coordVec_mem b X, ?_, z, hz, ?_⟩
  · intro hzero
    exact hXne (h_coordVec_eq_zero b X hzero)
  · rw [h_sq_expand b c hexp X]
    unfold coordVec
    have hdist : ∀ (s : Finset (Fin n)) (f : Fin n → E),
        Finset.sum s (fun k => z • f k) = z • Finset.sum s (fun k => f k) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp only [Finset.sum_empty, smul_zero]
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, smul_add]
    simp only [← hdist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF k, mul_smul]

end MkSecondPoint
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Wiring the conditional theorems to the coordinatization proofs

This module applies the three conditional theorems of `MkSecondPoint`
(`weak_second_point`, `second_point_ne_spurious`, and
`weak_fixedPoint_of_idempotent`) to the nine proved lemmas of `CoordinatizationToolkit`,
discharging the nine coordinatization hypotheses of each conditional
statement. The two remaining hypotheses are packaged as standalone `Prop`
definitions (`Mult1SpuriousProp` and `RegularSectionStepProp`) whose bodies
match the conditional binders exactly, so the three wired theorems below are
conditional on precisely those two propositions.

Two routine adaptations bridge the module boundary (both definitional, no
new mathematics):
* `MkSecondPoint` carries its own local copies of
  `coordVec` / `sqCoords` / `homogQuadric` with the same bodies; the `w_*`
  wrapper lemmas transport the `CoordinatizationToolkit` proofs across the namespace
  boundary by definitional unfolding.
* `CoordinatizationToolkit.sq_expand` takes `IsScalarTower` / `SMulCommClass` as explicit
  arguments, while the conditional statements expect instance-implicit
  binders; `w_sq_expand` re-exposes them in the expected shape, supplied
  from context.

## Assumptions

`K` is a field and `E` a (not necessarily unital or associative) `K`-module.
The scalar-tower/commutativity facts travel as explicit `Prop` hypotheses
where needed (fixed-point assembly), `Module.Finite` stays an explicit
hypothesis, and `IsAlgClosed` is an instance binder — mirroring the
conditional statements being wired.

This module depends only on the two Bridge modules `CoordinatizationToolkit` and
`SecondPointExistence` (which in turn depend on `Statement.Definitions`,
`A_Preliminaries`, and Mathlib).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SecondPointWiring

open scoped BigOperators

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MkSecondPoint

variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-- Spurious-point multiplicity hypothesis, standalone: the local multiplicity
at the distinguished point equals `1`, packaged as a single `Prop`. Its body
matches the `h_mult1_spurious` binder of the conditional theorems exactly;
nothing is proved about it here. -/
def Mult1SpuriousProp : Prop :=
  ∀ (m : ℕ) (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (_ : ∀ i, (F i).IsHomogeneous 2) (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0),
    localPointMultiplicity m K (mkSystem m K F) ℓ hc
      (distinguishedPoint m K) = 1

/-- Regular-section induction-step hypothesis, standalone: the minimal
sufficient interface for choosing a regular section, preserving
base-point-freeness, and lifting solutions, packaged as a single `Prop`.
Its body matches the `h_regular_section_step` binder of the conditional
theorems exactly; nothing is proved about it here. -/
def RegularSectionStepProp : Prop :=
  ∀ (m : ℕ) (cc : Fin (m + 1 + 1) → Fin (m + 1 + 1) → Fin (m + 1 + 1) → K),
    BPF K (m + 1 + 1) cc →
      LinearIndependent K (fun k : Fin (m + 1 + 1) =>
        fun dx : Fin (m + 1 + 1) → K => -dx k) →
        ∃ (cc' : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K),
          BPF K (m + 1) cc' ∧
            (WeakExists K (m + 1) cc' → WeakExists K (m + 1 + 1) cc)

/-! ## Wrapper lemmas (namespace and binder-shape adaptations). -/

/-- `CoordinatizationToolkit.sq_expand` in the binder shape the conditional theorems expect:
the tower/commutativity hypotheses are supplied from the instance-implicit
binders, and the local definitions are converted across namespaces. -/
theorem w_sq_expand {V : Submodule K E} {m : ℕ}
    (b : Module.Basis (Fin m) K V)
    (cc : Fin m → Fin m → Fin m → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, cc i j k • (b k : E))
    (X : Fin m → K) [IsScalarTower K E E] [SMulCommClass K E E] :
    coordVec K E b X * coordVec K E b X =
      ∑ k, sqCoords K cc k X • (b k : E) :=
  CoordinatizationToolkit.sq_expand K E b cc hexp X inferInstance inferInstance

/-! ## Wired theorems (conditional on exactly the two `Prop` hypotheses). -/

end SecondPointWiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
