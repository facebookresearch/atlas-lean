/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The associated graded ring `gr_I(R)` (Koszul-plan step A4(i))

Step A4(i) of the scoped Koszul/AB plan (A1–A6): the associated graded ring
`gr_I(R) = ⨁ₙ I^n / I^(n+1)` of a commutative ring `R` with respect to an
ideal `I`, with the `R_P` specialization (`I = maximalIdeal R_P`) that step
A4 (exactness of `K(sop)`, the crux of `DepthEqDimAt`) consumes.

Mathlib status: `ReesAlgebra.lean` carries only the Rees
algebra `R[It] ⊆ R[t]` for Artin–Rees; the associated graded ring itself is
absent and must be built. We build it on the `DirectSum` graded-ring
infrastructure (`GCommRing` gives `CommRing (⨁ n, grPiece R I n)`).

## Milestones

* (1) Graded pieces `I^n / I^(n+1)` as modules (§1): `grSub`, `grPiece` with
  induction and `mk` computation rules. Proved.
* (2) Multiplication on the direct sum (§2): `grMulRep` (bilinear on
  representatives) double-lifted through the quotients (`grMulQ1`,
  `grMulQ1Lin`, `grMulQ2`) to the `GMul`/`GOne` instances. Proved.
* (3) Ring laws (§3): `GMonoid` (unit/assoc laws via quotient induction plus
  cast along the index equation), `GSemiring`, `GRing`, `GCommRing`, hence
  `CommRing (associatedGraded R I)`. Proved.
* (4) Generation in degree 1 (§4): `grPiece_span_mul_eq_top` — every class in
  degree `1 + n` is an `R`-linear combination of degree-`(1, n)` products,
  i.e. `gr` is generated over its degree-0 part by `gr¹`. Proved. The
  canonical graded surjection from a polynomial ring is proved (M4b below).

## Remaining (milestone 4)

* (M4a) Degree-zero identification `grPiece R I 0 ≃+* R ⧸ I`. Proved (§5:
  `grPiece_zero_equiv_quotient`, via `liftQ` of `Ideal.Quotient.mk`, the
  `DirectSum`-scoped `Semiring (grPiece R I 0)`, and `grPiece_cast_mk`).
* (M4b) The canonical graded surjection
  `MvPolynomial (Fin d) (R ⧸ I) →+* associatedGraded R I` for `d` generators
  of `I`, via the universal property + `grPiece_span_mul_eq_top`. Proved in
  `Regularity/Koszul/GradedSurjection.lean` (`polySurj`).
* (M4c) Hilbert–Samuel + the gr-exactness lift (the remainder of A4).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/DirectSum/Ring.lean`: the `G*` graded-ring classes and the
  `DirectSum.commRing` / `of_mul_of` / `ofZeroRingHom` API.
* `Algebra/GradedMonoid.lean`: `GMul`, `GOne`, `GMonoid`, `GCommMonoid`.
* `LinearAlgebra/Quotient/Basic.lean` + `Defs.lean`: `mkQ`, `liftQ`,
  `Quotient.mk` / `Quotient.induction_on` / `Quotient.mk_eq_zero`.
* `LinearAlgebra/BilinearMap.lean`: `LinearMap.mk₂`.
* `RingTheory/Ideal/Operations.lean`: `Ideal.mul_mem_mul`, `Ideal.one_eq_top`
  (ideal powers split by the generic monoid `pow_add`).
* `RingTheory/ReesAlgebra.lean`: the Rees algebra (Artin–Rees only; the
  associated graded built here is new).
* `RingTheory/LocalRing/ResidueField/Defs.lean`: `IsLocalRing.ResidueField`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `Ideal.Quotient.mk` / `lift` (§5).
* `Algebra/Ring/Equiv.lean`: `RingEquiv.ofRingHom` (§5).

Project (read-only):
* `Regularity/Koszul/SystemOfParameters.lean` (step A1: the sop consumed by A2/A4).
* `Regularity/Koszul/KoszulComplex.lean` (step A2: the Koszul complex).

## Status

* `grMulRep`, `grMulQ1`, `grMulQ1Lin`, `grMulQ2`: unconditional.
* `GMonoid` / `GSemiring` / `GRing` / `GCommRing` instances: unconditional.
* `CommRing (associatedGraded R I)`: unconditional.
* `grPiece_span_mul_eq_top`: unconditional.
* `grPiece_zero_equiv_quotient` (§5, M4a): unconditional.
-/

open scoped Pointwise DirectSum

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AssociatedGradedRing

variable (R : Type*) [CommRing R] (I : Ideal R)

/-! ## §1. Graded pieces `I^n / I^(n+1)` (milestone 1) -/

/-- The submodule `I^(n+1)` viewed inside `↥(I^n)` via the subtype coercion:
the relations of the degree-`n` graded piece. -/
def grSub (n : ℕ) : Submodule R ↥(I ^ n) :=
  Submodule.comap (I ^ n).subtype (I ^ (n + 1))

/-- Membership in `grSub` unfolds to membership in `I^(n+1)`. -/
@[simp]
theorem mem_grSub_iff (n : ℕ) (a : ↥(I ^ n)) :
    a ∈ grSub R I n ↔ (a : R) ∈ I ^ (n + 1) :=
  Submodule.mem_comap

/-- The degree-`n` graded piece `I^n / I^(n+1)`. Reducible so that the
`Submodule.Quotient` API (induction, `mk` lemmas, `liftQ`) applies directly. -/
abbrev grPiece (n : ℕ) : Type _ :=
  (↥(I ^ n)) ⧸ (grSub R I n)

/-- Every class has a representative. -/
theorem grPiece_mk_surjective (n : ℕ) (x : grPiece R I n) :
    ∃ r, Submodule.Quotient.mk r = x :=
  Submodule.Quotient.mk_surjective (grSub R I n) x

/-- A class is zero iff its representative lies in `I^(n+1)`. -/
@[simp]
theorem grPiece_mk_eq_zero_iff (n : ℕ) (r : ↥(I ^ n)) :
    (Submodule.Quotient.mk r : grPiece R I n) = 0 ↔ (r : R) ∈ I ^ (n + 1) := by
  rw [Submodule.Quotient.mk_eq_zero, mem_grSub_iff]

/-- `mkQ` and `Quotient.mk` agree on graded pieces (definitionally). -/
@[simp]
theorem grPiece_mkQ_eq_mk (n : ℕ) (r : ↥(I ^ n)) :
    (grSub R I n).mkQ r = Submodule.Quotient.mk r :=
  rfl

/-- `mk` commutes with addition. -/
@[simp]
theorem grPiece_mk_add (n : ℕ) (a b : ↥(I ^ n)) :
    (Submodule.Quotient.mk a + Submodule.Quotient.mk b : grPiece R I n) =
      Submodule.Quotient.mk (a + b) := by
  calc Submodule.Quotient.mk a + Submodule.Quotient.mk b
      = (grSub R I n).mkQ a + (grSub R I n).mkQ b := by
        rw [grPiece_mkQ_eq_mk, grPiece_mkQ_eq_mk]
    _ = (grSub R I n).mkQ (a + b) := (map_add _ _ _).symm
    _ = Submodule.Quotient.mk (a + b) := grPiece_mkQ_eq_mk _ _ _ _

/-- `mk` commutes with scalar multiplication. -/
@[simp]
theorem grPiece_mk_smul (n : ℕ) (c : R) (a : ↥(I ^ n)) :
    (c • Submodule.Quotient.mk a : grPiece R I n) =
      Submodule.Quotient.mk (c • a) := by
  calc c • Submodule.Quotient.mk a
      = c • (grSub R I n).mkQ a := by rw [grPiece_mkQ_eq_mk]
    _ = (grSub R I n).mkQ (c • a) := (map_smul _ _ _).symm
    _ = Submodule.Quotient.mk (c • a) := grPiece_mkQ_eq_mk _ _ _ _

/-- `mk` commutes with negation. -/
@[simp]
theorem grPiece_mk_neg (n : ℕ) (a : ↥(I ^ n)) :
    (-Submodule.Quotient.mk a : grPiece R I n) =
      Submodule.Quotient.mk (-a) := by
  calc -Submodule.Quotient.mk a
      = -((grSub R I n).mkQ a) := by rw [grPiece_mkQ_eq_mk]
    _ = (grSub R I n).mkQ (-a) := (map_neg _ _).symm
    _ = Submodule.Quotient.mk (-a) := grPiece_mkQ_eq_mk _ _ _ _

/-! ## §2. Multiplication (milestone 2) -/

/-- Multiplication of representatives: `(a, b) ↦ a * b`, landing in
`I^(i+j)` by `Ideal.pow_add` + `Ideal.mul_mem_mul`.
-/
def grMulRep (i j : ℕ) : ↥(I ^ i) →ₗ[R] ↥(I ^ j) →ₗ[R] ↥(I ^ (i + j)) :=
  LinearMap.mk₂ R
    (fun a b => ⟨(a : R) * (b : R), by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.2 b.2⟩)
    (fun a₁ a₂ b => Subtype.ext (by
      change ((a₁ + a₂ : ↥(I ^ i)) : R) * (b : R) =
        (a₁ : R) * (b : R) + (a₂ : R) * (b : R)
      rw [show ((a₁ + a₂ : ↥(I ^ i)) : R) = (a₁ : R) + (a₂ : R) from rfl]
      exact add_mul _ _ _))
    (fun c a b => Subtype.ext (by
      change ((c • a : ↥(I ^ i)) : R) * (b : R) = c * ((a : R) * (b : R))
      rw [show ((c • a : ↥(I ^ i)) : R) = c * (a : R) from rfl]
      exact mul_assoc _ _ _))
    (fun a b₁ b₂ => Subtype.ext (by
      change (a : R) * ((b₁ + b₂ : ↥(I ^ j)) : R) =
        (a : R) * (b₁ : R) + (a : R) * (b₂ : R)
      rw [show ((b₁ + b₂ : ↥(I ^ j)) : R) = (b₁ : R) + (b₂ : R) from rfl]
      exact mul_add _ _ _))
    (fun c a b => Subtype.ext (by
      change (a : R) * ((c • b : ↥(I ^ j)) : R) = c * ((a : R) * (b : R))
      rw [show ((c • b : ↥(I ^ j)) : R) = c * (b : R) from rfl]
      exact mul_left_comm _ _ _))

/-- The representative product coerces to the product of coercions. -/
@[simp]
theorem grMulRep_apply (i j : ℕ) (a : ↥(I ^ i)) (b : ↥(I ^ j)) :
    ((grMulRep R I i j) a b : R) = (a : R) * (b : R) :=
  rfl

/-- First quotient lift, kernel side: for fixed `a`, the map `b ↦ a * b`
kills `I^(j+1)`, since `I^i * I^(j+1) = I^(i+j+1)`. -/
theorem grMulKer1 (i j : ℕ) (a : ↥(I ^ i)) :
    grSub R I j ≤
      LinearMap.ker (((grSub R I (i + j)).mkQ).comp ((grMulRep R I i j) a)) := by
  intro b hb
  rw [mem_grSub_iff] at hb
  rw [LinearMap.mem_ker, LinearMap.comp_apply, grPiece_mkQ_eq_mk,
    Submodule.Quotient.mk_eq_zero, mem_grSub_iff, grMulRep_apply]
  have hmem : (a : R) * (b : R) ∈ I ^ i * I ^ (j + 1) :=
    Ideal.mul_mem_mul a.2 hb
  have hpow : I ^ (i + j + 1) = I ^ i * I ^ (j + 1) := by
    rw [show i + j + 1 = i + (j + 1) from by omega, pow_add]
  rw [hpow]
  exact hmem

/-- First quotient lift: multiplication by a fixed representative, as a linear
map on the degree-`j` piece.
-/
def grMulQ1 (i j : ℕ) (a : ↥(I ^ i)) :
    grPiece R I j →ₗ[R] grPiece R I (i + j) :=
  (grSub R I j).liftQ
    (((grSub R I (i + j)).mkQ).comp ((grMulRep R I i j) a))
    (grMulKer1 R I i j a)

/-- `grMulQ1` on classes is `mk` of the representative product. -/
@[simp]
theorem grMulQ1_mk (i j : ℕ) (a : ↥(I ^ i)) (b : ↥(I ^ j)) :
    grMulQ1 R I i j a (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((grMulRep R I i j) a b) :=
  rfl

/-- The first lift is linear in the fixed representative.
-/
def grMulQ1Lin (i j : ℕ) :
    ↥(I ^ i) →ₗ[R] (grPiece R I j →ₗ[R] grPiece R I (i + j)) where
  toFun a := grMulQ1 R I i j a
  map_add' a₁ a₂ := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := grPiece_mk_surjective R I j x
    simp only [grMulQ1_mk, LinearMap.add_apply, grPiece_mk_add]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    change ((grMulRep R I i j) (a₁ + a₂) b : R) =
      ((grMulRep R I i j) a₁ b : R) + ((grMulRep R I i j) a₂ b : R)
    rw [grMulRep_apply, grMulRep_apply, grMulRep_apply]
    change ((a₁ + a₂ : ↥(I ^ i)) : R) * (b : R) =
      (a₁ : R) * (b : R) + (a₂ : R) * (b : R)
    rw [show ((a₁ + a₂ : ↥(I ^ i)) : R) = (a₁ : R) + (a₂ : R) from rfl]
    exact add_mul _ _ _
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := grPiece_mk_surjective R I j x
    simp only [grMulQ1_mk, LinearMap.smul_apply, grPiece_mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    change ((grMulRep R I i j) (c • a) b : R) =
      c • ((grMulRep R I i j) a b : R)
    rw [grMulRep_apply, grMulRep_apply]
    change ((c • a : ↥(I ^ i)) : R) * (b : R) = c * ((a : R) * (b : R))
    rw [show ((c • a : ↥(I ^ i)) : R) = c * (a : R) from rfl]
    exact mul_assoc _ _ _

/-- Second quotient lift, kernel side: the linearized first lift kills
`I^(i+1)`, since `I^(i+1) * I^j = I^(i+j+1)`. -/
theorem grMulKer2 (i j : ℕ) :
    grSub R I i ≤ LinearMap.ker (grMulQ1Lin R I i j) := by
  intro a ha
  rw [mem_grSub_iff] at ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := grPiece_mk_surjective R I j x
  change grMulQ1 R I i j a (Submodule.Quotient.mk b) = 0
  rw [grMulQ1_mk, grPiece_mk_eq_zero_iff, grMulRep_apply]
  have hmem : (a : R) * (b : R) ∈ I ^ (i + 1) * I ^ j :=
    Ideal.mul_mem_mul ha b.2
  have hpow : I ^ (i + j + 1) = I ^ (i + 1) * I ^ j := by
    rw [show i + j + 1 = (i + 1) + j from by omega, pow_add]
  rw [hpow]
  exact hmem

/-- Second quotient lift: the full graded multiplication, linear in each
argument separately.
-/
def grMulQ2 (i j : ℕ) :
    grPiece R I i →ₗ[R] (grPiece R I j →ₗ[R] grPiece R I (i + j)) :=
  (grSub R I i).liftQ (grMulQ1Lin R I i j) (grMulKer2 R I i j)

/-- `grMulQ2` on classes is `mk` of the representative product. -/
@[simp]
theorem grMulQ2_mk (i j : ℕ) (a : ↥(I ^ i)) (b : ↥(I ^ j)) :
    (grMulQ2 R I i j) (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((grMulRep R I i j) a b) := by
  rw [show (grMulQ2 R I i j) (Submodule.Quotient.mk a) =
    grMulQ1 R I i j a from rfl, grMulQ1_mk]

/-- Graded multiplication on pieces. -/
instance instGMul : GradedMonoid.GMul (grPiece R I) where
  mul {i j} a b := (grMulQ2 R I i j) a b

/-- The unit: the class of `1` in degree 0. -/
instance instGOne : GradedMonoid.GOne (grPiece R I) where
  one := Submodule.Quotient.mk
    (⟨1, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩ :
      ↥(I ^ 0))

/-- `GMul.mul` unfolds to the double lift (for `simp`). -/
@[simp]
theorem grMul_def (i j : ℕ) (a : grPiece R I i) (b : grPiece R I j) :
    GradedMonoid.GMul.mul a b = (grMulQ2 R I i j) a b :=
  rfl

/-- Graded multiplication on classes is `mk` of the representative product. -/
@[simp]
theorem grMul_mk_mk (i j : ℕ) (a : ↥(I ^ i)) (b : ↥(I ^ j)) :
    GradedMonoid.GMul.mul (A := grPiece R I)
        (Submodule.Quotient.mk a : grPiece R I i)
        (Submodule.Quotient.mk b : grPiece R I j) =
      Submodule.Quotient.mk ((grMulRep R I i j) a b) :=
  grMulQ2_mk R I i j a b

/-- The graded unit is the class of `1`. -/
theorem grOne_eq_mk : (GradedMonoid.GOne.one : grPiece R I 0) =
    Submodule.Quotient.mk (⟨1, by simp⟩ : ↥(I ^ 0)) :=
  rfl

/-! ## §3. Ring laws (milestone 3) -/

/-- Cast of a class along an index equation: `cast` pushes through `mk`. -/
theorem grPiece_cast_mk (n m : ℕ) (e : n = m) (s : ↥(I ^ n)) :
    cast (congrArg (grPiece R I) e) (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk ⟨(s : R), by rw [← e]; exact s.2⟩ := by
  subst e
  rfl

/-- Left unit law on representatives (heterogeneous form). -/
theorem grPiece_heq_one_mul (i : ℕ) (r : ↥(I ^ i)) :
    HEq (GradedMonoid.GMul.mul (A := grPiece R I)
        (GradedMonoid.GOne.one : grPiece R I 0)
        (Submodule.Quotient.mk r : grPiece R I i))
      (Submodule.Quotient.mk r : grPiece R I i) := by
  have hcast : cast (congrArg (grPiece R I) (zero_add i))
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (GradedMonoid.GOne.one : grPiece R I 0)
          (Submodule.Quotient.mk r : grPiece R I i)) =
        (Submodule.Quotient.mk r : grPiece R I i) := by
    rw [grOne_eq_mk, grMul_mk_mk, grPiece_cast_mk _ _ _ _ (zero_add i) _]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    simp only [grMulRep_apply]
    exact one_mul _
  exact heq_of_cast_eq _ hcast

/-- Left unit law on the graded monoid of pieces. -/
theorem grPiece_gMonoid_one_mul (a : GradedMonoid (grPiece R I)) :
    1 * a = a := by
  obtain ⟨i, x⟩ := a
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I i x
  exact Sigma.ext (zero_add i) (grPiece_heq_one_mul R I i r)

/-- Right unit law on representatives (heterogeneous form). -/
theorem grPiece_heq_mul_one (i : ℕ) (r : ↥(I ^ i)) :
    HEq (GradedMonoid.GMul.mul (A := grPiece R I)
        (Submodule.Quotient.mk r : grPiece R I i)
        (GradedMonoid.GOne.one : grPiece R I 0))
      (Submodule.Quotient.mk r : grPiece R I i) := by
  have hcast : cast (congrArg (grPiece R I) (add_zero i))
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk r : grPiece R I i)
          (GradedMonoid.GOne.one : grPiece R I 0)) =
        (Submodule.Quotient.mk r : grPiece R I i) := by
    rw [grOne_eq_mk, grMul_mk_mk, grPiece_cast_mk _ _ _ _ (add_zero i) _]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    simp only [grMulRep_apply]
    exact mul_one _
  exact heq_of_cast_eq _ hcast

/-- Right unit law on the graded monoid of pieces. -/
theorem grPiece_gMonoid_mul_one (a : GradedMonoid (grPiece R I)) :
    a * 1 = a := by
  obtain ⟨i, x⟩ := a
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I i x
  exact Sigma.ext (add_zero i) (grPiece_heq_mul_one R I i r)

/-- Associativity on representatives (heterogeneous form). -/
theorem grPiece_heq_mul_assoc (i j k : ℕ) (r : ↥(I ^ i)) (s : ↥(I ^ j))
    (t : ↥(I ^ k)) :
    HEq (GradedMonoid.GMul.mul (A := grPiece R I)
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk r : grPiece R I i)
          (Submodule.Quotient.mk s : grPiece R I j))
        (Submodule.Quotient.mk t : grPiece R I k))
      (GradedMonoid.GMul.mul (A := grPiece R I)
        (Submodule.Quotient.mk r : grPiece R I i)
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk s : grPiece R I j)
          (Submodule.Quotient.mk t : grPiece R I k))) := by
  have hcast : cast (congrArg (grPiece R I) (add_assoc i j k))
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (GradedMonoid.GMul.mul (A := grPiece R I)
            (Submodule.Quotient.mk r : grPiece R I i)
            (Submodule.Quotient.mk s : grPiece R I j))
          (Submodule.Quotient.mk t : grPiece R I k)) =
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk r : grPiece R I i)
          (GradedMonoid.GMul.mul (A := grPiece R I)
            (Submodule.Quotient.mk s : grPiece R I j)
            (Submodule.Quotient.mk t : grPiece R I k))) := by
    simp only [grMul_mk_mk]
    rw [grPiece_cast_mk _ _ _ _ (add_assoc i j k) _]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    simp only [grMulRep_apply]
    exact mul_assoc _ _ _
  exact heq_of_cast_eq _ hcast

/-- Associativity on the graded monoid of pieces. -/
theorem grPiece_gMonoid_mul_assoc (a b c : GradedMonoid (grPiece R I)) :
    a * b * c = a * (b * c) := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain ⟨k, z⟩ := c
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I i x
  obtain ⟨s, rfl⟩ := grPiece_mk_surjective R I j y
  obtain ⟨t, rfl⟩ := grPiece_mk_surjective R I k z
  exact Sigma.ext (add_assoc i j k) (grPiece_heq_mul_assoc R I i j k r s t)

/-- Commutativity on representatives (heterogeneous form). -/
theorem grPiece_heq_mul_comm (i j : ℕ) (r : ↥(I ^ i)) (s : ↥(I ^ j)) :
    HEq (GradedMonoid.GMul.mul (A := grPiece R I)
        (Submodule.Quotient.mk r : grPiece R I i)
        (Submodule.Quotient.mk s : grPiece R I j))
      (GradedMonoid.GMul.mul (A := grPiece R I)
        (Submodule.Quotient.mk s : grPiece R I j)
        (Submodule.Quotient.mk r : grPiece R I i)) := by
  have hcast : cast (congrArg (grPiece R I) (add_comm i j))
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk r : grPiece R I i)
          (Submodule.Quotient.mk s : grPiece R I j)) =
        (GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk s : grPiece R I j)
          (Submodule.Quotient.mk r : grPiece R I i)) := by
    simp only [grMul_mk_mk]
    rw [grPiece_cast_mk _ _ _ _ (add_comm i j) _]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    simp only [grMulRep_apply]
    exact mul_comm _ _
  exact heq_of_cast_eq _ hcast

/-- Commutativity on the graded monoid of pieces (from `R` commutative). -/
theorem grPiece_gCommMonoid_mul_comm (a b : GradedMonoid (grPiece R I)) :
    a * b = b * a := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I i x
  obtain ⟨s, rfl⟩ := grPiece_mk_surjective R I j y
  exact Sigma.ext (add_comm i j) (grPiece_heq_mul_comm R I i j r s)

/-- Graded additive/multiplicative compatibility, from linearity of `grMulQ2`.
-/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (grPiece R I) where
  mul_zero a := by simp [grMul_def]
  zero_mul b := by simp [grMul_def]
  mul_add a b c := by simp [grMul_def]
  add_mul a b c := by simp [grMul_def]

/-- The graded monoid structure on pieces.
-/
instance instGMonoid : GradedMonoid.GMonoid (grPiece R I) where
  one_mul := grPiece_gMonoid_one_mul R I
  mul_one := grPiece_gMonoid_mul_one R I
  mul_assoc := grPiece_gMonoid_mul_assoc R I

/-- The graded semiring structure on pieces.
-/
instance instGSemiring : DirectSum.GSemiring (grPiece R I) where
  natCast n := Submodule.Quotient.mk
    (⟨(n : R), by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩ :
      ↥(I ^ 0))
  natCast_zero := by
    change Submodule.Quotient.mk _ = (0 : grPiece R I 0)
    rw [grPiece_mk_eq_zero_iff]
    change ((0 : ℕ) : R) ∈ I ^ (0 + 1)
    rw [Nat.cast_zero]
    exact Submodule.zero_mem _
  natCast_succ n := by
    change Submodule.Quotient.mk _ =
      Submodule.Quotient.mk _ + GradedMonoid.GOne.one
    rw [grOne_eq_mk, grPiece_mk_add]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    change (((n + 1 : ℕ)) : R) = (n : R) + 1
    push_cast
    ring

/-- The graded ring structure on pieces.
-/
instance instGRing : DirectSum.GRing (grPiece R I) where
  intCast n := Submodule.Quotient.mk
    (⟨(n : R), by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩ :
      ↥(I ^ 0))
  intCast_ofNat n := by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    change (((n : ℕ) : ℤ) : R) = ((n : ℕ) : R)
    exact Int.cast_natCast _
  intCast_negSucc_ofNat n := by
    change Submodule.Quotient.mk _ = -Submodule.Quotient.mk _
    rw [grPiece_mk_neg]
    refine congrArg Submodule.Quotient.mk ?_
    refine Subtype.ext ?_
    change ((Int.negSucc n : ℤ) : R) = -(((n + 1 : ℕ)) : R)
    exact Int.cast_negSucc _

/-- The graded commutative monoid structure on pieces.
-/
instance instGCommMonoid : GradedMonoid.GCommMonoid (grPiece R I) where
  mul_comm := grPiece_gCommMonoid_mul_comm R I

/-- The graded commutative semiring structure on pieces.
-/
instance instGCommSemiring : DirectSum.GCommSemiring (grPiece R I) where

/-- The graded commutative ring structure on pieces.
-/
instance instGCommRing : DirectSum.GCommRing (grPiece R I) where

/-- The associated graded ring `gr_I(R) = ⨁ₙ I^n / I^(n+1)`. -/
def associatedGraded : Type _ :=
  DirectSum ℕ (grPiece R I)

/-- The commutative ring structure on the associated graded ring.
-/
instance instCommRing : CommRing (associatedGraded R I) :=
  DirectSum.commRing (grPiece R I)

/-- Multiplication of homogeneous elements adds degrees. -/
theorem associatedGraded_of_mul_of (i j : ℕ) (a : grPiece R I i)
    (b : grPiece R I j) :
    DirectSum.of (grPiece R I) i a * DirectSum.of (grPiece R I) j b =
      DirectSum.of (grPiece R I) (i + j) (GradedMonoid.GMul.mul a b) :=
  DirectSum.of_mul_of (A := grPiece R I) a b

/-! ## §4. Generation in degree 1 + the `R_P` specialization (milestone 4 input) -/

/-- Generation in degree 1: every class in degree `1 + n` is an `R`-linear
combination of products of degree-1 and degree-`n` classes, i.e. `gr` is
generated over its degree-0 part by `gr¹`. The proof is span induction on
`I^(1+n) = I^1 * I^n`: generators are products by `grMul_mk_mk`, and the
congruence closure follows the `mk` computation rules.

This is the key algebraic input to milestone (4) (the graded surjection from
a polynomial ring); see remaining (M4a–M4c) in the module docstring.
-/
theorem grPiece_span_mul_eq_top (n : ℕ) :
    Submodule.span R {z : grPiece R I (1 + n) | ∃ a : grPiece R I 1,
      ∃ b : grPiece R I n, GradedMonoid.GMul.mul a b = z} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I (1 + n) z
  have hmem : (r : R) ∈ Submodule.span R
      (((I ^ 1 : Ideal R) : Set R) * ((I ^ n : Ideal R) : Set R)) := by
    have hr : (r : R) ∈ I ^ 1 * I ^ n := by
      rw [← pow_add]
      exact r.2
    rwa [Submodule.mul_eq_span_mul_set] at hr
  have hle : Submodule.span R
      (((I ^ 1 : Ideal R) : Set R) * ((I ^ n : Ideal R) : Set R)) ≤
      I ^ (1 + n) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [pow_add]
    exact Ideal.mul_mem_mul ha hb
  have r_eq : r = (⟨(r : R), hle hmem⟩ : ↥(I ^ (1 + n))) := rfl
  rw [r_eq]
  refine Submodule.span_induction (p := fun x hx => Submodule.Quotient.mk
    (⟨x, hle hx⟩ : ↥(I ^ (1 + n))) ∈ Submodule.span R
      {z : grPiece R I (1 + n) | ∃ a : grPiece R I 1, ∃ b : grPiece R I n,
        GradedMonoid.GMul.mul a b = z}) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hmul : GradedMonoid.GMul.mul (A := grPiece R I)
          (Submodule.Quotient.mk (⟨a, ha⟩ : ↥(I ^ 1)) : grPiece R I 1)
          (Submodule.Quotient.mk (⟨b, hb⟩ : ↥(I ^ n)) : grPiece R I n) =
        Submodule.Quotient.mk
          (⟨a * b, hle (Submodule.subset_span ⟨a, ha, b, hb, rfl⟩)⟩ :
          ↥(I ^ (1 + n))) := by
      rw [grMul_mk_mk]
      refine congrArg Submodule.Quotient.mk ?_
      refine Subtype.ext ?_
      change ((grMulRep R I 1 n) _ _ : R) = a * b
      rw [grMulRep_apply]
    rw [← hmul]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  · have h0 : (Submodule.Quotient.mk
        (⟨(0 : R), hle (Submodule.zero_mem _)⟩ : ↥(I ^ (1 + n))) :
        grPiece R I (1 + n)) = 0 := by
      rw [grPiece_mk_eq_zero_iff]
      exact Submodule.zero_mem _
    rw [h0]
    exact Submodule.zero_mem _
  · intro x y hx hy ihx ihy
    have hadd : (Submodule.Quotient.mk
          (⟨x + y, hle (Submodule.add_mem _ hx hy)⟩ : ↥(I ^ (1 + n))) :
          grPiece R I (1 + n)) =
        Submodule.Quotient.mk (⟨x, hle hx⟩ : ↥(I ^ (1 + n))) +
          Submodule.Quotient.mk (⟨y, hle hy⟩ : ↥(I ^ (1 + n))) := by
      rw [grPiece_mk_add]
      refine congrArg Submodule.Quotient.mk ?_
      exact Subtype.ext rfl
    rw [hadd]
    exact Submodule.add_mem _ ihx ihy
  · intro c x hx ihx
    have hsmul : (Submodule.Quotient.mk
          (⟨c • x, hle (Submodule.smul_mem _ _ hx)⟩ : ↥(I ^ (1 + n))) :
          grPiece R I (1 + n)) =
        c • Submodule.Quotient.mk (⟨x, hle hx⟩ : ↥(I ^ (1 + n))) := by
      rw [grPiece_mk_smul]
      refine congrArg Submodule.Quotient.mk ?_
      exact Subtype.ext rfl
    rw [hsmul]
    exact Submodule.smul_mem _ _ ihx

/-! ## §4b. The `R_P` specialization -/

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The associated graded ring of the regular local ring `R_P` at a prime `P`,
with respect to its maximal ideal. The regular-local instance on `R_P` is
automatic (see `SystemOfParameters`); step A4 consumes this ring via milestone (4)
(the graded surjection from a polynomial ring over the residue field
`IsLocalRing.ResidueField R_P`). -/
def grRegular : Type _ :=
  associatedGraded (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))

/-- `grRegular` is a commutative ring.
-/
noncomputable instance grRegularCommRing : CommRing (grRegular P) :=
  instCommRing (Localization.AtPrime P) (IsLocalRing.maximalIdeal _)

/-! ## §5. Degree zero is `R ⧸ I` (M4a)

The degree-0 piece `grPiece R I 0 = ↥(I^0) ⧸ grSub R I 0` is `R ⧸ I` as a
ring: `I^0 = ⊤`, so representatives are all of `R`, and the relations are
`I^(0+1) = I`. The forward map is `liftQ` of `Ideal.Quotient.mk`
(`grPiece_zero_to_quotient`); its `map_mul` goes through the
`DirectSum`-scoped `Semiring (grPiece R I 0)` via `grPiece_zero_mul_mk`
(which unfolds the degree-0 product through `GradedMonoid.mk_zero_smul`
and `grPiece_cast_mk`). The backward map is `Ideal.Quotient.lift`
(`grPiece_zero_of_quotient`).

§5 additionally uses (Mathlib, read-only):
* `RingTheory/Ideal/Quotient/Defs.lean`: `Ideal.Quotient.mk` / `lift` /
  `lift_mk` / `mk_surjective` (all `rfl`-computation rules).
* `Algebra/Ring/Equiv.lean`: `RingEquiv.ofRingHom`.
* `Algebra/GradedMonoid.lean`: `GradedMonoid.mk_zero_smul`.
-/

/-- Degree-0 `One`, restated with `A := grPiece R I` so typeclass
resolution fires on unfolded `mk`-term types (the global
`GradedMonoid.GradeZero.one`, whose conclusion is `One (?A 0)`, cannot
match them by higher-order unification). Definitionally the `GOne` unit. -/
instance instOneZero : One (grPiece R I 0) :=
  GradedMonoid.GradeZero.one (grPiece R I)

/-- Degree-0 `Mul`, restated with `A := grPiece R I` so typeclass
resolution fires on unfolded `mk`-term types (the global
`GradedMonoid.GradeZero.mul`, whose conclusion is `Mul (?A 0)`, cannot
match them by higher-order unification). Definitionally the graded
product cast along `zero_add 0`. -/
instance instMulZero : Mul (grPiece R I 0) :=
  GradedMonoid.GradeZero.mul (grPiece R I)

/-- Multiplication in degree 0 on representatives: the `DirectSum`-scoped
`Semiring (grPiece R I 0)` multiplies classes by casting the graded product
along `zero_add 0` (via `GradedMonoid.mk_zero_smul`), hence on
representatives it is `mk` of the product of coercions. -/
theorem grPiece_zero_mul_mk (a b : ↥(I ^ 0)) :
    ((Submodule.Quotient.mk a : grPiece R I 0) *
      (Submodule.Quotient.mk b : grPiece R I 0)) =
      Submodule.Quotient.mk (⟨(a : R) * (b : R), by simp⟩ : ↥(I ^ 0)) := by
  have hsig : GradedMonoid.mk (A := grPiece R I) 0
          (Submodule.Quotient.mk a : grPiece R I 0) *
        GradedMonoid.mk (A := grPiece R I) 0
          (Submodule.Quotient.mk b : grPiece R I 0) =
      GradedMonoid.mk (A := grPiece R I) 0
        ((Submodule.Quotient.mk a : grPiece R I 0) *
          (Submodule.Quotient.mk b : grPiece R I 0)) :=
    (GradedMonoid.mk_zero_smul (A := grPiece R I)
      (Submodule.Quotient.mk a : grPiece R I 0)
      (Submodule.Quotient.mk b : grPiece R I 0)).symm
  have hsig2 : (⟨0 + 0, GradedMonoid.GMul.mul
        (Submodule.Quotient.mk a : grPiece R I 0)
        (Submodule.Quotient.mk b : grPiece R I 0)⟩ :
        GradedMonoid (grPiece R I)) =
      ⟨0, (Submodule.Quotient.mk a : grPiece R I 0) *
        (Submodule.Quotient.mk b : grPiece R I 0)⟩ := hsig
  obtain ⟨_, hheq⟩ := Sigma.ext_iff.1 hsig2
  have hheq' : HEq (GradedMonoid.GMul.mul
          (Submodule.Quotient.mk a : grPiece R I 0)
          (Submodule.Quotient.mk b : grPiece R I 0) : grPiece R I (0 + 0))
        ((Submodule.Quotient.mk a : grPiece R I 0) *
          (Submodule.Quotient.mk b : grPiece R I 0) : grPiece R I 0) :=
    hheq
  rw [grMul_mk_mk] at hheq'
  have hcast_of_heq : ∀ {i j : ℕ} (e : i = j) (x : grPiece R I i)
      (y : grPiece R I j),
      HEq x y → cast (congrArg (grPiece R I) e) x = y := by
    intro i j e x y h
    subst e
    exact eq_of_heq h
  have hmain := hcast_of_heq (zero_add 0)
    (Submodule.Quotient.mk (((grMulRep R I 0 0) a) b))
    ((Submodule.Quotient.mk a : grPiece R I 0) *
      (Submodule.Quotient.mk b : grPiece R I 0)) hheq'
  rw [grPiece_cast_mk _ _ _ _ (zero_add 0) _] at hmain
  rw [← hmain]
  refine congrArg Submodule.Quotient.mk ?_
  refine Subtype.ext ?_
  exact grMulRep_apply R I 0 0 a b

/-- Kernel side of the forward map: `mkQ ∘ coe` kills `grSub R I 0` since
`I ^ (0 + 1) = I`. -/
theorem grPiece_zero_to_quotient_ker :
    grSub R I 0 ≤
      LinearMap.ker (((I : Submodule R R).mkQ).comp (I ^ 0).subtype) := by
  intro a ha
  rw [mem_grSub_iff] at ha
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change ((I : Submodule R R).mkQ) (a : R) = 0
  have hmk : ((I : Submodule R R).mkQ) (a : R) =
      Submodule.Quotient.mk (a : R) := rfl
  rw [hmk, Submodule.Quotient.mk_eq_zero]
  have h01 : I ^ (0 + 1) = I := by rw [zero_add, pow_one]
  rw [h01] at ha
  exact ha

/-- The forward map as a linear map: `liftQ` of `mkQ ∘ coe`. -/
def grPiece_zero_to_quotient_lin : grPiece R I 0 →ₗ[R] R ⧸ I :=
  (grSub R I 0).liftQ (((I : Submodule R R).mkQ).comp (I ^ 0).subtype)
    (grPiece_zero_to_quotient_ker R I)

/-- The forward ring hom `gr⁰ →+* R ⧸ I`: the `liftQ` linear map upgraded
with `map_one`/`map_mul` through the `DirectSum`-scoped `Semiring`
(`grPiece_zero_mul_mk`). -/
def grPiece_zero_to_quotient : grPiece R I 0 →+* R ⧸ I where
  toFun := grPiece_zero_to_quotient_lin R I
  map_one' := by
    have h1 : (1 : grPiece R I 0) =
        Submodule.Quotient.mk (⟨1, by simp⟩ : ↥(I ^ 0)) := grOne_eq_mk R I
    rw [h1]
    exact map_one (Ideal.Quotient.mk I)
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := grPiece_mk_surjective R I 0 x
    obtain ⟨b, rfl⟩ := grPiece_mk_surjective R I 0 y
    rw [grPiece_zero_mul_mk]
    exact map_mul (Ideal.Quotient.mk I) _ _
  map_zero' := map_zero (grPiece_zero_to_quotient_lin R I)
  map_add' := fun x y => map_add (grPiece_zero_to_quotient_lin R I) x y

/-- Computation rule for the forward map. -/
@[simp]
theorem grPiece_zero_to_quotient_mk (s : ↥(I ^ 0)) :
    grPiece_zero_to_quotient R I (Submodule.Quotient.mk s) =
      Ideal.Quotient.mk I (s : R) :=
  rfl

/-- The ring hom `R →+* gr⁰` sending `r` to the class of `r`. -/
def grPiece_zero_of_quotient_fun : R →+* grPiece R I 0 where
  toFun r := Submodule.Quotient.mk (⟨r, by simp⟩ : ↥(I ^ 0))
  map_one' := (grOne_eq_mk R I).symm
  map_mul' a b := (grPiece_zero_mul_mk R I ⟨a, by simp⟩ ⟨b, by simp⟩).symm
  map_zero' := by
    change Submodule.Quotient.mk (⟨0, by simp⟩ : ↥(I ^ 0)) = 0
    rw [grPiece_mk_eq_zero_iff]
    exact Submodule.zero_mem _
  map_add' a b := (grPiece_mk_add R I 0 ⟨a, by simp⟩ ⟨b, by simp⟩).symm

/-- The backward ring hom `R ⧸ I →+* gr⁰` via `Ideal.Quotient.lift`. -/
def grPiece_zero_of_quotient : R ⧸ I →+* grPiece R I 0 :=
  Ideal.Quotient.lift I (grPiece_zero_of_quotient_fun R I) (fun a ha => by
    change Submodule.Quotient.mk (⟨a, by simp⟩ : ↥(I ^ 0)) = 0
    rw [grPiece_mk_eq_zero_iff]
    have h01 : I ^ (0 + 1) = I := by rw [zero_add, pow_one]
    rw [h01]
    exact ha)

/-- Computation rule for the backward map. -/
@[simp]
theorem grPiece_zero_of_quotient_mk (r : R) :
    grPiece_zero_of_quotient R I (Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk (⟨r, by simp⟩ : ↥(I ^ 0)) :=
  rfl

/-- Degree-zero identification `gr⁰ ≃+* R ⧸ I` (M4a).
-/
def grPiece_zero_equiv_quotient : grPiece R I 0 ≃+* R ⧸ I :=
  RingEquiv.ofRingHom (grPiece_zero_to_quotient R I)
    (grPiece_zero_of_quotient R I)
    (by
      refine RingHom.ext fun y => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp only [RingHom.comp_apply, grPiece_zero_of_quotient_mk,
        grPiece_zero_to_quotient_mk, RingHom.id_apply])
    (by
      refine RingHom.ext fun x => ?_
      obtain ⟨s, rfl⟩ := grPiece_mk_surjective R I 0 x
      simp only [RingHom.comp_apply, grPiece_zero_to_quotient_mk,
        grPiece_zero_of_quotient_mk, RingHom.id_apply])

#print axioms grPiece_span_mul_eq_top
#print axioms grMulQ2_mk
#print axioms associatedGraded_of_mul_of
#print axioms grPiece_zero_equiv_quotient

end AssociatedGradedRing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

