/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ProjectiveToConeExtraction
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MkSystemSmoothness
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective fixed point from Bézout

Derives the projective fixed-point principle
(`EvolutionAlgebras.fixedPoint_of_idempotent`, paper Theorem `idempotentiff`,
backward direction) from a Bézout theorem for quadrics in projective space.

Outline (classical: fixed point of `x ↦ x * x` on `ℙ(V)`):
1. **Spine.** Work on the Ring spine (documented below), so `Basis`/finrank
   machinery applies.
2. **Coordinatize.** From `Module.Finite` + `V ≠ ⊥` get a finite basis of `V`;
   the squaring map becomes coordinate quadrics `Fᵢ` via structure constants.
3. **Homogenize.** `Gᵢ = Fᵢ - z * xᵢ` in `n + 1` homogeneous variables;
   `[0:1]` is always a solution and is smooth (linear parts `-xᵢ` independent).
4. **Bézout + `N(V) = {0}`.** A second `K`-point exists; `z ≠ 0` there, since
   points with `z = 0` satisfy `F(x) = 0`, forcing `x = 0` by `hN` (not a
   projective point).
5. **Dehomogenize.** Scale to `z = 1` and read off `x * x = lam • x`.

Do not add this file to `EvolutionAlgebras.lean` imports (it is pulled
in transitively). Do not import
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement` or
`Geometry.Counting` (DAG rule) — their results enter as verbatim-shape
hypotheses (`hStatementInst`, `hSecondOfNotZd`); `Statement.Definitions`,
`BridgeToFixedPoint.ProjectiveToConeExtraction`, `BridgeToFixedPoint.MkSystemSmoothness` are
imported (clean, cycle-free).

## Main results

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.fixedPoint_fromBezout`: the fixed-point
  principle
  deduced from `bezout_quadrics` (conclusion propositionally matches
  `EvolutionAlgebras.fixedPoint_of_idempotent` up to ∃-mem sugar, Ring spine
  vs minimal spine, and extra tower/comm binders).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/- Spine decision (outline step 1): use the Ring spine
`[Field K] [NonUnitalNonAssocRing E] [Module K E]`, not the minimal `A_FixedPoint` spine
`[Field K] [NonUnitalNonAssocSemiring E] [Module K E]`.
Rationale: coordinatization needs `Module.Basis`, `finrank`, and the
`AddCommGroup` API, all of which require `AddCommGroup E`; the minimal spine
provides only `AddCommMonoid E` and has no homogeneity/finrank lemmas, so we do
not fight it — we pick the spine that works. `NonUnitalNonAssocRing` extends
*both* `AddCommGroup` and `NonUnitalNonAssocSemiring` from one root, so there
is exactly one additive path (no diamond), `square` is still fed by
instance, and the conclusion propositionally matches
`fixedPoint_of_idempotent` up to ∃-mem sugar, Ring spine vs minimal spine,
and extra tower/comm binders, so a later merge can adapt it. -/
variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/- General-function placeholder (old `bezout_quadrics` function form): refuted —
see `bezout_quadrics_counterexample` / `bezout_quadrics_general_isFalse` below
(witness `G k X z = X k * X k` at `n = 1`). The corrected mkSystem-shape
conditional theorem reuses the name `bezout_quadrics` below. -/

/-- Coordinatization, existence (outline step 2, proved below):
over a field, a finite nonzero submodule has a finite basis indexed by
`Fin n` with `n ≥ 1` (via `finrank > 0` / a nonzero vector in `V`). -/
theorem exists_pos_fin_basis (V : Submodule K E)
    (hfin : Module.Finite K E) (hneV : V ≠ ⊥) :
    ∃ (n : ℕ) (_ : 0 < n), Nonempty (Module.Basis (Fin n) K V) := by
  have hfinV : Module.Finite K V :=
    @FiniteDimensional.finiteDimensional_submodule K E _ _ _ hfin V
  have hnt : Nontrivial V := (Submodule.nontrivial_iff_ne_bot).mpr hneV
  have hpos : 0 < Module.finrank K V :=
    ((@Module.finrank_pos_iff_of_free K V _ _ _ _ _ hfinV).mpr hnt)
  exact ⟨Module.finrank K V, hpos,
    ⟨@Module.finBasisOfFinrankEq K V _ _ _ _ _ hfinV _ rfl⟩⟩

/-- Structure constants (outline step 2, proved below): basis products
land back in `V` by idempotence (`V² = V`), hence expand in the basis. -/
theorem exists_structure_constants {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (hV : IsIdempotentSubmodule K E V) :
    ∃ c : Fin n → Fin n → Fin n → K,
      ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E) := by
  have hsq : square K E V = V := hV
  have hmem : ∀ i j : Fin n, (b i : E) * (b j : E) ∈ V := by
    intro i j
    have hgen : (b i : E) * (b j : E) ∈ square K E V := by
      apply Submodule.subset_span
      exact ⟨(b i : E), (b i).property, (b j : E), (b j).property, rfl⟩
    rwa [hsq] at hgen
  refine ⟨fun i j k => b.repr ⟨(b i : E) * (b j : E), hmem i j⟩ k, fun i j => ?_⟩
  have hrep := b.sum_repr ⟨(b i : E) * (b j : E), hmem i j⟩
  have hcon := congrArg (⇑V.subtype) hrep
  rw [map_sum] at hcon
  simp only [map_smul, Submodule.subtype_apply] at hcon
  exact hcon.symm

/-- Coordinate vector: the element of `E` with coordinates `X` in the basis `b`. -/
noncomputable def coordVec {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : E :=
  ∑ i, X i • (b i : E)

/-- Quadrics of the squaring map: `Fₖ(X)` is the `k`-th coordinate of `v(X)²`. -/
def sqCoords {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) : K :=
  ∑ i, ∑ j, c i j k * X i * X j

/-- Homogenized system `Gₖ(X, z) = Fₖ(X) - z * Xₖ` (outline step 3). -/
def homogQuadric {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) (z : K) : K :=
  sqCoords K c k X - z * X k

/-- Coordinate vectors lie in `V` (sums of scalar multiples of basis vectors). -/
theorem coordVec_mem {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : coordVec K E b X ∈ V := by
  unfold coordVec
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact (b i).property

/-- The distinguished point is always a solution (outline step 3, proved):
`F(0) = 0` since every monomial of a quadric vanishes at `0`, so
`Gₖ(0, 1) = 0 - 1 * 0 = 0`. -/
theorem distinguished_isSolution {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) : homogQuadric K c k 0 1 = 0 := by
  simp [homogQuadric, sqCoords]

/-- Bilinear expansion of the square in coordinates (outline steps 4–5, proved
below): `(∑ᵢ Xᵢbᵢ)² = ∑ₖ Fₖ(X) bₖ`, by distributivity of `*` over `+`
and scalar interchange through the product. -/
theorem sq_expand {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (X : Fin n → K) [IsScalarTower K E E] [SMulCommClass K E E] :
    coordVec K E b X * coordVec K E b X =
      ∑ k, sqCoords K c k X • (b k : E) := by
  have hsm : ∀ (a b : K) (u v : E), (a • u) * (b • v) = (a * b) • (u * v) := by
    intro a b u v
    rw [smul_mul_assoc, mul_smul_comm, ← smul_smul]
  have hscalar : ∀ i j k : Fin n,
      (X i * X j) * c i j k = c i j k * X i * X j := by
    intro i j k
    rw [mul_comm (X i * X j) (c i j k), ← mul_assoc]
  have hper : ∀ i j : Fin n,
      (X i • (b i : E)) * (X j • (b j : E)) =
        ∑ k, (c i j k * X i * X j) • (b k : E) := by
    intro i j
    have h1 : (X i • (b i : E)) * (X j • (b j : E))
        = (X i * X j) • ((b i : E) * (b j : E)) :=
      hsm (X i) (X j) _ _
    rw [h1, hexp i j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, hscalar i j k]
  have hswap : ∀ f : Fin n → Fin n → Fin n → E,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    intro f
    calc ∑ i, ∑ j, ∑ k, f i j k
        = ∑ i, ∑ k, ∑ j, f i j k := by
          congr 1
          ext i
          exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
  have hR : (∑ k, sqCoords K c k X • (b k : E))
      = ∑ k, ∑ i, ∑ j, (c i j k * X i * X j) • (b k : E) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqCoords
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
  unfold coordVec
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, hper]
  rw [hswap, ← hR]

/-- Coordinates are faithful (proved below): the basis images
`(bₖ : E)` are linearly independent in `E`, so `v(X) = 0` forces `X = 0`. -/
theorem coordVec_eq_zero {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Fin n → K)
    (h : coordVec K E b X = 0) : X = 0 := by
  have hindep : LinearIndependent K (V.subtype ∘ b) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hsum : ∑ i, X i • (V.subtype ∘ b) i = 0 := h
  have hX : ∀ i, X i = 0 := Fintype.linearIndependent_iff.mp hindep X hsum
  funext i
  exact hX i

/-- Smoothness at the distinguished point (outline step 3, proved below):
the linear parts of `G` at `(0, 1)` are the forms `-xₖ` (the Jacobian there is
`[-I | 0]`, rank `n`), which are linearly independent — so `[0:1]` is a smooth
`K`-point of multiplicity one. -/
theorem distinguished_smooth (n : ℕ) :
    LinearIndependent K (fun k : Fin n => fun dx : Fin n → K => -dx k) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h0 := congrFun hg (Pi.single (M := fun _ => K) i (1 : K))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hsum : ∑ j ∈ s, g j * (-(Pi.single (M := fun _ => K) i (1 : K) j)) = -(g i) := by
    calc ∑ j ∈ s, g j * (-(Pi.single (M := fun _ => K) i (1 : K) j))
        = g i * (-(Pi.single (M := fun _ => K) i (1 : K) i)) :=
          Finset.sum_eq_single_of_mem i hi (fun j _ hji => by
            have hzero : Pi.single (M := fun _ => K) i (1 : K) j = 0 := by
              simp [hji]
            simp [hzero])
      _ = -(g i) := by simp
  rw [hsum] at h0
  exact neg_eq_zero.mp h0

/-- Quadratic homogeneity of the coordinate quadrics (proved): each monomial
of `Fₖ` has total degree 2, so `Fₖ(a • X) = a² * Fₖ(X)`. -/
theorem sqCoords_hom {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) (a : K) (X : Fin n → K) :
    sqCoords K c k (a • X) = a ^ 2 * sqCoords K c k X := by
  simp only [sqCoords, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `N(V) = {0}` hypothesis as an elementwise rule (proved): a vector of
`V` squaring to zero is zero. -/
theorem eq_zero_of_mem_sq_eq_zero (V : Submodule K E)
    (hN : absNilpotent K E V = {0}) {x : E} (hx : x ∈ V) (hxx : x * x = 0) :
    x = 0 := by
  have hmem : x ∈ absNilpotent K E V := ⟨hx, hxx⟩
  rw [hN] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- Refutation witness for the general-function placeholder (refuted).
At `n = 1`, `G 0 X z = X 0 * X 0` satisfies `hG0` (vanishes at `(0,1)`),
`hGhom` (quadratic scaling, `z` ignored), and the G-independent `hsmooth`
(`distinguished_smooth`), yet every zero has `X = 0` (since `a * a = 0 →
a = 0`), so no `(X, z)` with `X ≠ 0` exists. Hence the old universal
`bezout_quadrics` (for arbitrary `G`) is false; only the mkSystem-shape
narrowing (below) is derivable. -/
theorem bezout_quadrics_counterexample :
    ∃ (G : Fin 1 → (Fin 1 → K) → K → K),
      (∀ k, G k 0 1 = 0) ∧
      (∀ (k : Fin 1) (a : K) (X : Fin 1 → K) (z : K),
        G k (a • X) (a * z) = a ^ 2 * G k X z) ∧
      LinearIndependent K (fun k : Fin 1 => fun dx : Fin 1 → K => -dx k) ∧
      ¬ ∃ (X : Fin 1 → K) (z : K), (∀ k, G k X z = 0) ∧ X ≠ 0 := by
  refine ⟨fun k X _ => X k * X k, ?_, ?_, distinguished_smooth K 1, ?_⟩
  · intro k
    simp
  · intro k a X z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨X, z, hsol, hne⟩
    apply hne
    funext k
    exact mul_self_eq_zero.mp (hsol k)

/-- The old general-function `bezout_quadrics` statement is false: its
universal claim (over all `n`, `G`, and premises) is negated by
`bezout_quadrics_counterexample` at `n = 1`. Stated in the old placeholder's
context (`[IsAlgClosed K]`), so the placeholder is unclosable as written. -/
theorem bezout_quadrics_general_isFalse [IsAlgClosed K] :
    ¬ ∀ {n : ℕ} (_hn : 0 < n)
      (G : Fin n → (Fin n → K) → K → K)
      (_hG0 : ∀ k, G k 0 1 = 0)
      (_hGhom : ∀ (k : Fin n) (a : K) (X : Fin n → K) (z : K),
        G k (a • X) (a * z) = a ^ 2 * G k X z)
      (_hsmooth : LinearIndependent K
        (fun k : Fin n => fun dx : Fin n → K => -dx k)),
      ∃ (X : Fin n → K) (z : K), (∀ k, G k X z = 0) ∧ X ≠ 0 := by
  intro hAll
  obtain ⟨G, hG0, hGhom, hsmooth, hNo⟩ := bezout_quadrics_counterexample K
  exact hNo (hAll (n := 1) (by norm_num) G hG0 hGhom hsmooth)

/-! ## T1/T2 embedding (step 2; duplicated from
`MkSystemBridge`, which cannot be imported here — it imports this file, so an
import would cycle; proofs verbatim, only docstrings shortened). -/

/-- Statement-level index `n_Statement = n_placeholder − 1` (T1a). -/
def statementIndex (n : ℕ) : ℕ := n - 1

/-- The shift cancels for `0 < n`. -/
theorem shift_add_one (n : ℕ) (hn : 0 < n) : statementIndex n + 1 = n :=
  Nat.sub_add_cancel hn

/-- Equation-index equivalence transported along the shift. -/
def shiftEquiv (n : ℕ) (hn : 0 < n) : Fin (statementIndex n + 1) ≃ Fin n :=
  finCongr (shift_add_one n hn)

/-- Quadratic-form polynomials from structure constants (T1b). -/
noncomputable def mkQuadForm (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) : MvPolynomial (Fin N) K :=
  ∑ i, ∑ j, MvPolynomial.C (c i j k) * (MvPolynomial.X i * MvPolynomial.X j)

/-- Evaluation recovers `sqCoords`. -/
theorem eval_mkQuadForm (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) (X : Fin N → K) :
    MvPolynomial.eval X (mkQuadForm N K c k)
      = sqCoords K c k X := by
  unfold mkQuadForm sqCoords
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]

/-- Each quadratic-form polynomial is homogeneous of degree `2` (T2). -/
theorem mkQuadForm_isHomogeneous (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) :
    (mkQuadForm N K c k).IsHomogeneous 2 := by
  unfold mkQuadForm
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa using (MvPolynomial.isHomogeneous_C _ _).mul
    ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- Reindexed structure constants along the shift equivalence. -/
noncomputable def shiftConsts (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1) → Fin (statementIndex n + 1)
      → Fin (statementIndex n + 1) → K :=
  fun i j k => c (shiftEquiv n hn i) (shiftEquiv n hn j) (shiftEquiv n hn k)

/-- Statement-level quadratic forms from shifted constants. -/
noncomputable def bridgeForms (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1) → MvPolynomial (Fin (statementIndex n + 1)) K :=
  fun k => mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) k

/-- The instantiated `mkSystem` for placeholder data (T1 output). -/
noncomputable def bridgeSystem (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1)
      → MvPolynomial (Fin (statementIndex n + 2)) K :=
  mkSystem (statementIndex n) K (bridgeForms n K c hn)

/-- Homogeneity of the bridge forms (feeds `mkSystem_homogeneous`). -/
theorem bridgeForms_homogeneous (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ i, ((bridgeForms n K c hn) i).IsHomogeneous 2 := by
  intro i
  change (mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) i).IsHomogeneous 2
  exact mkQuadForm_isHomogeneous _ K _ _

/-- `mkSystem` evaluation splits as `Fᵢ(x) − z·xᵢ` (eval-bridge step 1). -/
theorem bridgeSystem_eval (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) (v : Fin (m + 2) → K) :
    MvPolynomial.eval v (mkSystem m K F i)
      = MvPolynomial.eval (fun j => v (Fin.castSucc j)) (F i)
        - v (Fin.last (m + 1)) * v (Fin.castSucc i) := by
  unfold mkSystem
  rw [map_sub, MvPolynomial.eval_rename, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X]
  rfl

/-- The instantiated system is homogeneous (Statement `hG` shape; proof is
`Statement.mkSystem_homogeneous`'s, inlined since `Statement` is not imported
per the DAG rule — verbatim-shape hypotheses instead). -/
theorem bridgeSystem_homogeneous (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 := by
  intro i
  simp only [bridgeSystem, mkSystem]
  exact ((bridgeForms_homogeneous n K c hn i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-! ## Cone transport (step 6). -/

/-- `sqCoords` is invariant under reindexing structure constants along an
equivalence (both sums reindexed via `Equiv.sum_comp` under `[hX]`). -/
theorem sqCoords_shift (M n : ℕ) (K : Type*) [Field K] (e : Fin M ≃ Fin n)
    (c : Fin n → Fin n → Fin n → K)
    (X' : Fin M → K) (X : Fin n → K) (i : Fin M)
    (hX : ∀ j, X' j = X (e j)) :
    sqCoords K (fun p q r => c (e p) (e q) (e r)) i X'
      = sqCoords K c (e i) X := by
  unfold sqCoords
  change (∑ p, ∑ q, c (e p) (e q) (e i) * X' p * X' q)
      = ∑ p', ∑ q', c p' q' (e i) * X p' * X q'
  have inner : ∀ p : Fin M,
      (∑ q, c (e p) (e q) (e i) * X (e p) * X (e q))
        = ∑ q', c (e p) q' (e i) * X (e p) * X q' :=
    fun p => Equiv.sum_comp e
      (fun q' : Fin n => c (e p) q' (e i) * X (e p) * X q')
  simp_rw [hX, inner]
  exact Equiv.sum_comp e
    (fun p' : Fin n => ∑ q', c p' q' (e i) * X p' * X q')

/-- Eval-bridge at the combined vector: polynomial evaluation of the bridge
system equals `homogQuadric` (combines `bridgeSystem_eval` + `eval_mkQuadForm`
+ `sqCoords_shift` + `Fin.lastCases` computation, under `[hX]`). -/
theorem eval_bridgeSystem_eq_homogQuadric {n : ℕ} (K : Type*) [Field K]
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (X : Fin n → K) (X' : Fin (statementIndex n + 1) → K) (z : K)
    (hX : ∀ j, X' j = X (shiftEquiv n hn j))
    (i : Fin (statementIndex n + 1)) :
    MvPolynomial.eval (Fin.lastCases (motive := fun _ => K) z X')
        (bridgeSystem n K c hn i)
      = homogQuadric K c (shiftEquiv n hn i) X z := by
  have hsplit := bridgeSystem_eval (statementIndex n) K (bridgeForms n K c hn) i
    (Fin.lastCases (motive := fun _ => K) z X')
  have hx : (fun j => Fin.lastCases (motive := fun _ => K) z X' (Fin.castSucc j))
      = X' := by
    funext j
    simp
  have hz : Fin.lastCases (motive := fun _ => K) z X'
      (Fin.last (statementIndex n + 1)) = z := by
    simp
  have hcast : Fin.lastCases (motive := fun _ => K) z X' (Fin.castSucc i)
      = X (shiftEquiv n hn i) := by
    rw [show Fin.lastCases (motive := fun _ => K) z X' (Fin.castSucc i) = X' i
      from by simp]
    exact hX i
  have hF : MvPolynomial.eval X' (bridgeForms n K c hn i)
      = sqCoords K c (shiftEquiv n hn i) X := by
    change MvPolynomial.eval X'
      (mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) i) = _
    rw [eval_mkQuadForm]
    change sqCoords K
      (fun p q r => c (shiftEquiv n hn p) (shiftEquiv n hn q)
        (shiftEquiv n hn r)) i X' = _
    exact sqCoords_shift (statementIndex n + 1) n K (shiftEquiv n hn) c X' X i hX
  change MvPolynomial.eval (Fin.lastCases (motive := fun _ => K) z X')
    (mkSystem (statementIndex n) K (bridgeForms n K c hn) i) = _
  rw [hsplit, hx, hz, hcast, hF]
  rw [show homogQuadric K c (shiftEquiv n hn i) X z
    = sqCoords K c (shiftEquiv n hn i) X - z * X (shiftEquiv n hn i) from rfl]

/-- Projective-to-cone extraction at the bridge system (T7 assembly): a locus
point distinct from the distinguished point yields `(X, z)` with
`∀ k, homogQuadric … = 0` and `X ≠ 0` (via `ProjectiveToConeExtraction.exists_conePair…` +
the eval-bridge, transporting `Fin (m+1)` to `Fin n` along `shiftEquiv`). -/
theorem conePoint_of_secondPoint {n : ℕ} (K : Type*) [Field K] (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (q : Projectivization K (Fin (statementIndex n + 2) → K))
    (hmem : q ∈ vanishingLocus (statementIndex n) K (bridgeSystem n K c hn))
    (hne : q ≠ distinguishedPoint (statementIndex n) K) :
    ∃ (X : Fin n → K) (z : K), (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  obtain ⟨X', z, -, heval, hX'ne⟩ :=
    exists_conePair_of_mem_ne_distinguishedPoint (statementIndex n) K
      (bridgeSystem n K c hn) q hmem hne
  set X : Fin n → K := fun k => X' ((shiftEquiv n hn).symm k) with hXdef
  have hX : ∀ j, X' j = X (shiftEquiv n hn j) := by
    intro j
    simp only [hXdef]
    rw [Equiv.symm_apply_apply (shiftEquiv n hn) j]
  refine ⟨X, z, ?_, ?_⟩
  · intro k
    have hi := heval ((shiftEquiv n hn).symm k)
    have hbr := eval_bridgeSystem_eq_homogQuadric K hn c X X' z hX
      ((shiftEquiv n hn).symm k)
    rw [Equiv.apply_symm_apply (shiftEquiv n hn) k] at hbr
    rw [hbr] at hi
    exact hi
  · intro hX0
    apply hX'ne
    funext j
    rw [hX j, hX0]
    simp

/-! ## Corrected Bézout at mkSystem shape (T8 assembly). -/

/-- Corrected `bezout_quadrics` at mkSystem shape (Conditional, exact
list below): from structure constants `c`, the `homogQuadric` system has a
cone zero `(X, z)` with `X ≠ 0` — via the `n−1` shift (T1), `mkSystem`
homogeneity (T2), distinguished-point inputs `hmem`/`hsmooth`/`hmult` wired
through `MkSystemSmoothness.distinguished_inputs_mkSystem` (T3, reusing
`Counting.smooth_of_negId_linear_parts` + `smooth_implies_mult_one`),
case split on `hZd` (`Statement.exists_another_point_of_smooth_point` /
`¬hZd`-branch), and cone extraction with `X ≠ 0` (T7).

conditional on exactly: `ℓ`, `hc`, `hreg` (R1/T4: `havoid`/`hcover`/`hS`
open; `hc` is the ∀-p chart-nonvanishing the local form
requires), `H F hH0 hSES hSEC hfilter` (count numerics:
`hSES`/`hSEC`/`hfilter` open, leaves L-R2/L-R1/L-FILT), `hfin hsum hbridge
hpos` (point-counting, now in local `localPointMultiplicity` form:
open modulo L-COVER/L-LOCAL/L-ADD/L-HLIN/L-POS), `hloc` (T6 locality for
`hmult`, now the local `localMultiplicity … = 1` shape, L-SMOOTH-VAL),
`hStatementInst` (verbatim import of the proved point-counting corollary
in local form —
`Statement` not imported per the DAG rule), `hSecondOfNotZd` (verbatim
`¬hZd`-branch second point; discharges via
`Counting.infinite_locus_of_not_zeroDim` + `hcontra`, L-CONTRA).

Local-form resolution: `hmult` pins
the local length at `distinguishedPoint.rep` (`= 1`) while `hbridge` +
the section count pin the global chart length (`= 2^(n+1) ≥ 2`) — jointly
consistent, so neither branch is vacuous on its face. The derivation
structure (wiring + transport) is unaffected. -/
theorem bezout_quadrics {n : ℕ} [IsAlgClosed K] (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (ℓ : Fin (statementIndex n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (statementIndex n + 2) → K))
      (_ : p ∈ vanishingLocus (statementIndex n) K (bridgeSystem n K c hn))
      (v : Fin (statementIndex n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p
        → MvPolynomial.eval v (mkLin (statementIndex n) K ℓ) ≠ 0)
    (hreg : IsSMulRegular (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
      (Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
        (mkLin (statementIndex n) K ℓ)))
    (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hH0 : ∀ d, H 0 d
      = Nat.choose (d + (statementIndex n + 2) - 1) ((statementIndex n + 2) - 1))
    (hSES : ∀ k, k < statementIndex n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      F d + (if 1 ≤ d then H (statementIndex n + 1) (d - 1) else 0)
        = H (statementIndex n + 1) d)
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F d) ∧
      ∀ d, B < d → F d = 0)
    (hfin : (vanishingLocus (statementIndex n) K (bridgeSystem n K c hn)).Finite)
    (hsum : ∑ p ∈ hfin.toFinset,
        localPointMultiplicity (statementIndex n) K (bridgeSystem n K c hn) ℓ hc p
      = Module.finrank K
        (chartRing (statementIndex n) K (bridgeSystem n K c hn) ℓ))
    (hbridge : Module.finrank K
        (chartRing (statementIndex n) K (bridgeSystem n K c hn) ℓ)
      = totalDegree (statementIndex n) K (bridgeSystem n K c hn) ℓ)
    (hpos : ∀ p ∈ hfin.toFinset,
      1 ≤ localPointMultiplicity (statementIndex n) K (bridgeSystem n K c hn) ℓ hc p)
    (hloc : localMultiplicity (statementIndex n) K (bridgeSystem n K c hn) ℓ
      (distinguishedPoint (statementIndex n) K).rep
      (fun i => mem_vanishingLocus_mkSystem (statementIndex n) K
        (bridgeForms n K c hn) (bridgeForms_homogeneous n K c hn)
        (distinguishedPoint (statementIndex n) K).rep
        (distinguishedPoint (statementIndex n) K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint (statementIndex n) K)) i)
      (hc (distinguishedPoint (statementIndex n) K)
        (mem_vanishingLocus_mkSystem (statementIndex n) K
          (bridgeForms n K c hn) (bridgeForms_homogeneous n K c hn))
        (distinguishedPoint (statementIndex n) K).rep
        (distinguishedPoint (statementIndex n) K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint (statementIndex n) K))) = 1)
    (hStatementInst : ∀
      (_hG' : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2)
      (ℓ' : Fin (statementIndex n + 2) → K)
      (hc' : ∀ (p : Projectivization K (Fin (statementIndex n + 2) → K))
        (_ : p ∈ vanishingLocus (statementIndex n) K (bridgeSystem n K c hn))
        (v : Fin (statementIndex n + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p
          → MvPolynomial.eval v (mkLin (statementIndex n) K ℓ') ≠ 0)
      (_hreg' : IsSMulRegular
        (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
        (Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K ℓ')))
      (_hZd' : IsZeroDimensional (statementIndex n) K (bridgeSystem n K c hn))
      (_hmem' : distinguishedPoint (statementIndex n) K ∈
        vanishingLocus (statementIndex n) K (bridgeSystem n K c hn))
      (_hsmooth' : IsSmoothPoint (statementIndex n) K (bridgeSystem n K c hn)
        (distinguishedPoint (statementIndex n) K))
      (_hmult' : localPointMultiplicity (statementIndex n) K
        (bridgeSystem n K c hn) ℓ' hc'
        (distinguishedPoint (statementIndex n) K) = 1)
      (H' : ℕ → ℕ → ℕ) (F' : ℕ → ℕ)
      (_hH0' : ∀ d, H' 0 d
        = Nat.choose (d + (statementIndex n + 2) - 1)
          ((statementIndex n + 2) - 1))
      (_hSES' : ∀ k, k < statementIndex n + 1 → ∀ d,
        H' (k + 1) d + (if 2 ≤ d then H' k (d - 2) else 0) = H' k d)
      (_hSEC' : ∀ d,
        F' d + (if 1 ≤ d then H' (statementIndex n + 1) (d - 1) else 0)
          = H' (statementIndex n + 1) d)
      (_hfilter' : ∃ (B : ℕ)
        (Cf : ℕ → Submodule K
          (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn) ℓ')),
        Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
        (∀ d, d ≤ B →
          Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F' d) ∧
        ∀ d, B < d → F' d = 0)
      (hfin' : (vanishingLocus (statementIndex n) K
        (bridgeSystem n K c hn)).Finite)
      (_hsum' : ∑ p ∈ hfin'.toFinset,
          localPointMultiplicity (statementIndex n) K
            (bridgeSystem n K c hn) ℓ' hc' p
        = Module.finrank K
          (chartRing (statementIndex n) K (bridgeSystem n K c hn) ℓ'))
      (_hbridge' : Module.finrank K
          (chartRing (statementIndex n) K (bridgeSystem n K c hn) ℓ')
        = totalDegree (statementIndex n) K (bridgeSystem n K c hn) ℓ')
      (_hpos' : ∀ p ∈ hfin'.toFinset,
        1 ≤ localPointMultiplicity (statementIndex n) K
          (bridgeSystem n K c hn) ℓ' hc' p),
      ∃ q : Projectivization K (Fin (statementIndex n + 2) → K),
        q ∈ vanishingLocus (statementIndex n) K (bridgeSystem n K c hn) ∧
          q ≠ distinguishedPoint (statementIndex n) K)
    (hSecondOfNotZd : ¬ IsZeroDimensional (statementIndex n) K
        (bridgeSystem n K c hn) →
      ∃ q : Projectivization K (Fin (statementIndex n + 2) → K),
        q ∈ vanishingLocus (statementIndex n) K (bridgeSystem n K c hn) ∧
          q ≠ distinguishedPoint (statementIndex n) K) :
    ∃ (X : Fin n → K) (z : K), (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  obtain ⟨hmem_pf, hsmooth_pf, hmult_pf⟩ := distinguished_inputs_mkSystem
    (statementIndex n) K (bridgeForms n K c hn) ℓ
    (bridgeForms_homogeneous n K c hn) hc hloc
  rcases Classical.em
    (IsZeroDimensional (statementIndex n) K (bridgeSystem n K c hn))
    with hZdCase | hZdCase
  · obtain ⟨q, hmem_q, hne_q⟩ := hStatementInst
      (bridgeSystem_homogeneous n K c hn) ℓ hc hreg hZdCase hmem_pf hsmooth_pf
      hmult_pf H F hH0 hSES hSEC hfilter hfin hsum hbridge hpos
    exact conePoint_of_secondPoint K hn c q hmem_q hne_q
  · obtain ⟨q, hmem_q, hne_q⟩ := hSecondOfNotZd hZdCase
    exact conePoint_of_secondPoint K hn c q hmem_q hne_q

/-- Projective fixed-point theorem from Bézout (outline steps 4–5 assembled):
with `V² = V`, `N(V) = {0}`, `V ≠ ⊥` over an algebraically closed field, the
squaring map has a projective fixed point. Hypothesis names/roles match
`EvolutionAlgebras.fixedPoint_of_idempotent` (`hfin`, `hV`, `hN`, `hneV`) so a
later merge can adapt the result; the conclusion propositionally matches
`fixedPoint_of_idempotent` up to ∃-mem sugar, Ring spine vs minimal spine,
and extra tower/comm binders.

Conditional on `hBez` (universal cone-point existence over all
`(n, c)`). `hBez` discharges via corrected `bezout_quadrics` + the
∀-geometric open list; dehomogenization here (steps 4–5:
`z ≠ 0` via `hN`, `sq_expand`) is the non-circular content. -/
theorem fixedPoint_fromBezout (V : Submodule K E) [IsAlgClosed K]
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    [IsScalarTower K E E] [SMulCommClass K E E]
    (hBez : ∀ {n : ℕ} (_hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      ∃ (X : Fin n → K) (z : K), (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0) :
    -- Note: `lam : K` ascription is load-bearing: without it Lean defaults the
    -- flexibly-typed `∃ lam,...` binder to `ℕ` (via the `AddMonoid` nsmul
    -- instance), not `K`. Propositionally this matches `fixedPoint_of_idempotent`.
    ∃ x ∈ V, x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  obtain ⟨n, hn, hb⟩ := exists_pos_fin_basis K E V hfin hneV
  obtain ⟨b⟩ := hb
  obtain ⟨c, hexp⟩ := exists_structure_constants K E b hV
  obtain ⟨X, z, hsol, hXne⟩ := hBez hn c
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
      rw [sq_expand K E b c hexp X]
      simp [hF0]
    have hzero : coordVec K E b X = 0 :=
      eq_zero_of_mem_sq_eq_zero K E V hN (coordVec_mem K E b X) hsq0
    exact hXne (coordVec_eq_zero K E b X hzero)
  refine ⟨coordVec K E b X, coordVec_mem K E b X, ?_, z, hz, ?_⟩
  · intro hzero
    exact hXne (coordVec_eq_zero K E b X hzero)
  · rw [sq_expand K E b c hexp X]
    unfold coordVec
    -- `•` distributes over `∑` (proved inline: no such lemma name exists in the
    -- imported Mathlib fragment, so use `Finset.induction` + `smul_add`).
    have hdist : ∀ (s : Finset (Fin n)) (f : Fin n → E),
        Finset.sum s (fun k => z • f k) = z • Finset.sum s (fun k => f k) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, smul_add]
    simp only [← hdist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF k, mul_smul]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/- Status:
refuted (false): old general-function `bezout_quadrics` —
`bezout_quadrics_counterexample` + `bezout_quadrics_general_isFalse`
(witness `G k X z = X k * X k` at `n = 1`).
conditional: corrected `bezout_quadrics` (mkSystem shape, exact 16-hypothesis
geometric list + 2 verbatim imports, all multiplicity inputs in local
`localPointMultiplicity`/`localMultiplicity` form with `hc`; both branches
non-vacuous) and `fixedPoint_fromBezout`
(conditional on `hBez`, discharging via corrected `bezout_quadrics`).
Spliced in (from scratch files):
`exists_pos_fin_basis`, `exists_structure_constants`, `sq_expand`,
`coordVec_eq_zero`, `distinguished_smooth`.
Duplicated (cycle-safe, attributed): T1/T2 from `MkSystemBridge`
(`statementIndex` … `bridgeSystem_homogeneous`); T3 via imported
`MkSystemSmoothness.distinguished_inputs_mkSystem`; T7 via imported
`ProjectiveToConeExtraction.exists_conePair_of_mem_ne_distinguishedPoint`.
Threading note: `sq_expand` (hence `fixedPoint_fromBezout`) carries
`[IsScalarTower K E E] [SMulCommClass K E E]` — scalar interchange needs them
(SolvableCorollary precedent); `A_FixedPoint.lean` absorbs these as explicit
Prop hypotheses in the final statement.
Proved here: `coordVec_mem`, `distinguished_isSolution`,
`sqCoords_hom`, `eq_zero_of_mem_sq_eq_zero`, `sqCoords_shift`,
`eval_bridgeSystem_eq_homogQuadric`, `conePoint_of_secondPoint`. -/
