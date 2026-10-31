/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Exterior-sum decomposition for the Koszul induction step (A4(iii), file 1 of 6)

For a commutative ring `R` and an `R`-module `M`, with `V = M × R`, this file
proves the missing exterior-sum decomposition (missing-1):

`extSplit k : ⋀[R]^(k+1) V ≃ₗ[R] (⋀[R]^(k+1) M) × (⋀[R]^k M)`.

* (§1) `exteriorPower.mapEquiv`: a linear equiv induces an equiv on exterior
  powers (helper for the `Fin` case).
* (§2) Generator lemmas: contraction along `snd` vanishes on the image of
  `inl`, and the reconstruction identity on `ιMulti` generators (span
  induction via `ιMulti_span_fixedDegree`-style `linearMap_ext`, plus
  `contractLeft_ι_mul`, `map_apply_ιMulti`, `ι_sq_zero`).
* (§3) Forward `(map fst, contract-along-snd)` reusing `koszulContract`,
  backward `map-inl + wedge(e_new, ·)` reusing `koszulD`, and the `extSplit`
  equiv with both inverse proofs.
* (§4) The `k = 0` case `extSplitZero : ⋀[R]^0 V ≃ₗ[R] ⋀[R]^0 M`.
* (§5) Differential matrices for both Koszul forms (cochain `koszulD` and
  chain `koszulContract`) from a charge-split hypothesis, plus the degree-0
  bottom map.
* (§6) The `Fin` case `extSplitFin` via `mapEquiv` + `Fin.consLinearEquiv`.

Design: direct span-induction route (route C). Mathlib's `prodEquivTensor`
route is deliberately not used (graded-tensor piece extraction costs more).

Project (read-only): `Regularity/Koszul/KoszulComplex.lean` (`koszulD`, `koszulContract`,
`koszulContract_mem`, `mem_ι_piece_one`, `mem_piece_one_iff`).

Consumers (sibling lanes): `KoszulConeSESBuild`, `ChainCone`, `AugmentedConeStep`.

Imported by `AugmentedConeStep`, `GrLiftAugmentation`, `TowerIdentification`, `ChainCone`
(consumers of `extSplit`/`extSplitZero`/`finSplitEquiv`).
-/

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-! ## §1. Exterior powers of a linear equiv -/

/-- A linear equiv induces a linear equiv on `n`-th exterior powers. -/
noncomputable def mapEquiv (e : M ≃ₗ[R] N) (n : ℕ) :
    ↥(⋀[R]^n M) ≃ₗ[R] ↥(⋀[R]^n N) where
  toLinearMap := exteriorPower.map n e.toLinearMap
  invFun := exteriorPower.map n e.symm.toLinearMap
  left_inv x := by
    change exteriorPower.map n e.symm.toLinearMap
      (exteriorPower.map n e.toLinearMap x) = x
    have h : exteriorPower.map n e.symm.toLinearMap ∘ₗ
        exteriorPower.map n e.toLinearMap = LinearMap.id := by
      rw [← exteriorPower.map_comp]
      have h2 : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
        ext y
        simp
      rw [h2, exteriorPower.map_id]
    exact LinearMap.congr_fun h x
  right_inv x := by
    change exteriorPower.map n e.toLinearMap
      (exteriorPower.map n e.symm.toLinearMap x) = x
    have h : exteriorPower.map n e.toLinearMap ∘ₗ
        exteriorPower.map n e.symm.toLinearMap = LinearMap.id := by
      rw [← exteriorPower.map_comp]
      have h2 : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
        ext y
        simp
      rw [h2, exteriorPower.map_id]
    exact LinearMap.congr_fun h x

/-- `mapEquiv` acts by `exteriorPower.map` of the underlying linear map. -/
@[simp]
theorem mapEquiv_apply (e : M ≃ₗ[R] N) (n : ℕ) (x : ↥(⋀[R]^n M)) :
    mapEquiv e n x = exteriorPower.map n e.toLinearMap x :=
  rfl

/-- The inverse of `mapEquiv` acts by `exteriorPower.map` of the inverse. -/
@[simp]
theorem mapEquiv_symm_apply (e : M ≃ₗ[R] N) (n : ℕ) (y : ↥(⋀[R]^n N)) :
    (mapEquiv e n).symm y = exteriorPower.map n e.symm.toLinearMap y :=
  rfl

end exteriorPower

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ExteriorSumDecomposition

open ExteriorAlgebra EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## §2. Generator lemmas: vanishing and reconstruction -/

/-- Contraction along `snd` vanishes on decomposable wedges from `inl`: every
generator dies by the antiderivation law since `snd (inl _) = 0`. -/
theorem contract_snd_ιMulti_inl (k : ℕ) (w : Fin k → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (LinearMap.snd R M R)
        (ExteriorAlgebra.ιMulti R k (LinearMap.inl R M R ∘ w)) = 0 := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply]
    exact CliffordAlgebra.contractLeft_one _ _
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply,
      CliffordAlgebra.contractLeft_ι_mul]
    have h0 : (LinearMap.snd R M R) ((LinearMap.inl R M R ∘ w) 0) = 0 := rfl
    rw [h0, zero_smul]
    have htail : Matrix.vecTail (LinearMap.inl R M R ∘ w) =
        LinearMap.inl R M R ∘ Matrix.vecTail w := rfl
    rw [htail, ih]
    simp

/-- Contraction along `snd` vanishes on the image of `inl` (all elements, via
`exteriorPower.linearMap_ext` span induction). -/
theorem contract_snd_map_inl (k : ℕ) (x : ↥(⋀[R]^k M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (LinearMap.snd R M R)
        ((exteriorPower.map k (LinearMap.inl R M R) x : ↥(⋀[R]^k (M × R))) :
          ExteriorAlgebra R (M × R)) = 0 := by
  have hL : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (LinearMap.snd R M R)).comp
        ((⋀[R]^k (M × R)).subtype.comp
          (exteriorPower.map k (LinearMap.inl R M R))) = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.coe_subtype, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, LinearMap.zero_apply]
    exact contract_snd_ιMulti_inl k v
  exact LinearMap.congr_fun hL x

/-- Algebra-level form of the vanishing lemma (for rewriting in normalized
goals where `exteriorPower.coe_map` has already fired). -/
theorem contract_snd_map_inl_alg (k : ℕ) (x : ↥(⋀[R]^k M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (LinearMap.snd R M R)
        (ExteriorAlgebra.map (LinearMap.inl R M R) (x : ExteriorAlgebra R M)) =
      0 := by
  have h := contract_snd_map_inl k x
  rwa [exteriorPower.coe_map] at h

/-- Contracting `e_new ∧ G1(y)` along `snd` recovers `G1(y)`: the
antiderivation law plus vanishing of the `e_new ∧ contract` remainder. -/
theorem contract_snd_wedge_new_alg (k : ℕ) (y : ↥(⋀[R]^k M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (LinearMap.snd R M R)
        (ExteriorAlgebra.ι R ((0, 1) : M × R) *
          ExteriorAlgebra.map (LinearMap.inl R M R)
            (y : ExteriorAlgebra R M)) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
        (y : ExteriorAlgebra R M) := by
  rw [CliffordAlgebra.contractLeft_ι_mul]
  have hsnd : (LinearMap.snd R M R) ((0, 1) : M × R) = 1 := rfl
  rw [hsnd, one_smul, contract_snd_map_inl_alg, mul_zero, sub_zero]

/-- The projection kills the new generator. -/
theorem map_fst_new :
    ExteriorAlgebra.map (LinearMap.fst R M R)
        (ExteriorAlgebra.ι R ((0, 1) : M × R)) = 0 := by
  rw [ExteriorAlgebra.map_apply_ι]
  have h : (LinearMap.fst R M R) ((0, 1) : M × R) = 0 := rfl
  rw [h, map_zero]

/-- `map fst ∘ map inl = id` on exterior powers (from `fst_comp_inl`). -/
theorem map_comp_fst_inl (n : ℕ) :
    (exteriorPower.map n (LinearMap.fst R M R)).comp
        (exteriorPower.map n (LinearMap.inl R M R)) = LinearMap.id := by
  rw [← exteriorPower.map_comp, LinearMap.fst_comp_inl, exteriorPower.map_id]

/-- Algebra-level form: `F1 (G1 x) = x`. -/
theorem map_fst_map_inl_coe (n : ℕ) (x : ↥(⋀[R]^n M)) :
    ExteriorAlgebra.map (LinearMap.fst R M R)
        (ExteriorAlgebra.map (LinearMap.inl R M R)
          (x : ExteriorAlgebra R M)) =
      (x : ExteriorAlgebra R M) := by
  have h := congrArg (fun y : ↥(⋀[R]^n M) => (y : ExteriorAlgebra R M))
    (LinearMap.congr_fun (map_comp_fst_inl n) x)
  simpa [exteriorPower.coe_map] using h

/-- The noncommutative algebra identity behind the induction step: with
`E * E = 0` and `A0 * E + E * A0 = 0`, forward-then-backward on a factored
generator agrees with the generator. -/
theorem cone_identity (A0 E Am B : ExteriorAlgebra R (M × R)) (r0 : R)
    (hE : E * E = 0) (hswap : A0 * E + E * A0 = 0) :
    A0 * Am + (r0 • (E * Am) - E * (A0 * B)) =
      (A0 + r0 • E) * (Am + E * B) := by
  have hanti : A0 * (E * B) = -(E * (A0 * B)) := by
    have h2 : (A0 * E + E * A0) * B = 0 := by rw [hswap, zero_mul]
    rw [add_mul] at h2
    rw [mul_assoc A0 E B, mul_assoc E A0 B] at h2
    exact eq_neg_iff_add_eq_zero.mpr h2
  rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc,
    ← mul_assoc E E B, hE, zero_mul, smul_zero, add_zero, hanti]
  abel

/-- Reconstruction identity on `ιMulti` generators (succ form, matching
`ιMulti_succ_apply` and `Matrix.vecTail` syntactically): mapping to `M` and
back, plus the `e_new`-wedge correction from contraction, recovers the
generator. HilbertFunctionCount on `k`, splitting off the head factor. -/
theorem reconstruct_ιMulti_succ (k : ℕ) (v : Fin k.succ → M × R) :
    ExteriorAlgebra.map (LinearMap.inl R M R)
        (ExteriorAlgebra.map (LinearMap.fst R M R)
          (ExteriorAlgebra.ιMulti R k.succ v))
      + ExteriorAlgebra.ι R ((0, 1) : M × R) *
        (ExteriorAlgebra.map (LinearMap.inl R M R)
          (ExteriorAlgebra.map (LinearMap.fst R M R)
            (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
              (LinearMap.snd R M R) (ExteriorAlgebra.ιMulti R k.succ v))))
      = ExteriorAlgebra.ιMulti R k.succ v := by
  induction k with
  | zero =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) (v := v)
    rw [hsplit, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
      ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
      CliffordAlgebra.contractLeft_ι]
    simp only [LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.snd_apply,
      AlgHom.commutes]
    have hvec : v 0 = ((v 0).1, (0 : R)) + (v 0).2 • (0, (1 : R)) := by
      ext <;> simp
    have hsmul : ExteriorAlgebra.ι R ((0, 1) : M × R) *
          algebraMap R (ExteriorAlgebra R (M × R)) (v 0).2
        = (v 0).2 • ExteriorAlgebra.ι R ((0, 1) : M × R) := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
    have hι : ExteriorAlgebra.ι R ((v 0).1, (0 : R))
          + (v 0).2 • ExteriorAlgebra.ι R ((0, 1) : M × R)
        = ExteriorAlgebra.ι R (v 0) := by
      rw [← map_smul, ← map_add]
      congr 1
      exact hvec.symm
    rw [hsmul]
    exact hι
  | succ k ih =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) (v := v)
    have hIH : ExteriorAlgebra.map (LinearMap.inl R M R)
            (ExteriorAlgebra.map (LinearMap.fst R M R)
              (ExteriorAlgebra.ιMulti R (k + 1) (Matrix.vecTail v)))
          + ExteriorAlgebra.ι R ((0, 1) : M × R) *
            (ExteriorAlgebra.map (LinearMap.inl R M R)
              (ExteriorAlgebra.map (LinearMap.fst R M R)
                (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
                  (LinearMap.snd R M R)
                  (ExteriorAlgebra.ιMulti R (k + 1) (Matrix.vecTail v)))))
          = ExteriorAlgebra.ιMulti R (k + 1) (Matrix.vecTail v) :=
      ih (Matrix.vecTail v)
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, ExteriorAlgebra.map_apply_ι,
      LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.snd_apply,
      mul_sub, mul_smul_comm]
    have hvec : v 0 = ((v 0).1, (0 : R)) + (v 0).2 • (0, (1 : R)) := by
      ext <;> simp
    have hι0 : ExteriorAlgebra.ι R (v 0)
          = ExteriorAlgebra.ι R ((v 0).1, 0)
            + (v 0).2 • ExteriorAlgebra.ι R ((0, 1) : M × R) := by
      rw [← map_smul, ← map_add]
      exact congrArg _ hvec
    have hE : ExteriorAlgebra.ι R ((0, 1) : M × R)
          * ExteriorAlgebra.ι R ((0, 1) : M × R) = 0 :=
      ExteriorAlgebra.ι_sq_zero _
    have hswap : ExteriorAlgebra.ι R ((v 0).1, (0 : R))
            * ExteriorAlgebra.ι R ((0, 1) : M × R)
          + ExteriorAlgebra.ι R ((0, 1) : M × R)
            * ExteriorAlgebra.ι R ((v 0).1, (0 : R)) = 0 := by
      rw [add_comm]
      exact ExteriorAlgebra.ι_add_mul_swap _ _
    conv_rhs => rw [hι0, ← hIH]
    exact cone_identity _ _ _ _ _ hE hswap

/-! ## §3. Forward, backward, and the `extSplit` equiv -/

/-- The new degree-one charge `e_new = ι (0, 1)`, the wedge factor for the
second backward component. -/
def newCharge : ↥(⋀[R]^1 (M × R)) :=
  ⟨ExteriorAlgebra.ι R ((0, 1) : M × R), mem_ι_piece_one _⟩

/-- Forward map: `(map fst, map fst ∘ contract-along-snd)`. -/
noncomputable def extSplitFwd (k : ℕ) :
    ↥(⋀[R]^(k + 1) (M × R)) →ₗ[R] ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M) :=
  LinearMap.prod (exteriorPower.map (k + 1) (LinearMap.fst R M R))
    ((exteriorPower.map k (LinearMap.fst R M R)).comp
      (koszulContract (LinearMap.snd R M R) k))

/-- Backward map: `map-inl + wedge(e_new, map-inl ·)`. -/
noncomputable def extSplitBwd (k : ℕ) :
    ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M) →ₗ[R] ↥(⋀[R]^(k + 1) (M × R)) :=
  LinearMap.coprod (exteriorPower.map (k + 1) (LinearMap.inl R M R))
    ((koszulD newCharge k).comp (exteriorPower.map k (LinearMap.inl R M R)))

/-- Coercion of the first component of `extSplitFwd`. -/
@[simp]
theorem extSplitFwd_fst_coe (k : ℕ) (z : ↥(⋀[R]^(k + 1) (M × R))) :
    (((extSplitFwd k z).1 : ↥(⋀[R]^(k + 1) M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.fst R M R)
        (z : ExteriorAlgebra R (M × R)) :=
  exteriorPower.coe_map _ _

/-- Coercion of the second component of `extSplitFwd`. -/
@[simp]
theorem extSplitFwd_snd_coe (k : ℕ) (z : ↥(⋀[R]^(k + 1) (M × R))) :
    (((extSplitFwd k z).2 : ↥(⋀[R]^k M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.fst R M R)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (LinearMap.snd R M R) (z : ExteriorAlgebra R (M × R))) :=
  (exteriorPower.coe_map (LinearMap.fst R M R)
    (koszulContract (LinearMap.snd R M R) k z)).trans
    (congrArg (ExteriorAlgebra.map (LinearMap.fst R M R))
      (koszulContract_apply (LinearMap.snd R M R) k z))

/-- Coercion of `extSplitBwd` through the exterior algebra. -/
@[simp]
theorem extSplitBwd_coe (k : ℕ) (p : ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M)) :
    ((extSplitBwd k p : ↥(⋀[R]^(k + 1) (M × R))) : ExteriorAlgebra R (M × R)) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
          ((p.1 : ↥(⋀[R]^(k + 1) M)) : ExteriorAlgebra R M)
        + ExteriorAlgebra.ι R ((0, 1) : M × R) *
          ExteriorAlgebra.map (LinearMap.inl R M R)
            ((p.2 : ↥(⋀[R]^k M)) : ExteriorAlgebra R M) := by
  change (((exteriorPower.map (k + 1) (LinearMap.inl R M R) p.1 +
      (koszulD newCharge k)
        (exteriorPower.map k (LinearMap.inl R M R) p.2) :
      ↥(⋀[R]^(k + 1) (M × R))) : ExteriorAlgebra R (M × R)) = _)
  rw [Submodule.coe_add, exteriorPower.coe_map, koszulD_apply,
    exteriorPower.coe_map]
  rfl

/-- Backward after forward is the identity (via the reconstruction identity on
generators). -/
theorem extSplitBwd_fwd (k : ℕ) (z : ↥(⋀[R]^(k + 1) (M × R))) :
    extSplitBwd k (extSplitFwd k z) = z := by
  have hcomp : (extSplitBwd k).comp (extSplitFwd k)
      = LinearMap.id (R := R) (M := ↥(⋀[R]^(k + 1) (M × R))) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    apply Subtype.ext
    rw [extSplitBwd_coe, extSplitFwd_fst_coe, extSplitFwd_snd_coe,
      exteriorPower.ιMulti_apply_coe]
    exact reconstruct_ιMulti_succ k v
  exact LinearMap.congr_fun hcomp z

/-- Forward after backward is the identity (both components direct). -/
theorem extSplitFwd_bwd (k : ℕ)
    (p : ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M)) :
    extSplitFwd k (extSplitBwd k p) = p := by
  obtain ⟨a, b⟩ := p
  apply Prod.ext
  · apply Subtype.ext
    rw [extSplitFwd_fst_coe, extSplitBwd_coe, map_add, map_mul, map_fst_new,
      zero_mul, add_zero]
    exact map_fst_map_inl_coe _ a
  · apply Subtype.ext
    rw [extSplitFwd_snd_coe, extSplitBwd_coe, map_add,
      contract_snd_map_inl_alg, contract_snd_wedge_new_alg, zero_add]
    exact map_fst_map_inl_coe _ b

/-- The exterior-sum decomposition. -/
noncomputable def extSplit (k : ℕ) :
    ↥(⋀[R]^(k + 1) (M × R)) ≃ₗ[R] ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M) where
  toLinearMap := extSplitFwd k
  invFun := extSplitBwd k
  left_inv := extSplitBwd_fwd k
  right_inv := extSplitFwd_bwd k

/-- `extSplit` unfolds to `extSplitFwd`. -/
@[simp]
theorem extSplit_apply (k : ℕ) (z : ↥(⋀[R]^(k + 1) (M × R))) :
    extSplit k z = extSplitFwd k z :=
  rfl

/-- The inverse of `extSplit` unfolds to `extSplitBwd`. -/
@[simp]
theorem extSplit_symm_apply (k : ℕ)
    (p : ↥(⋀[R]^(k + 1) M) × ↥(⋀[R]^k M)) :
    (extSplit k).symm p = extSplitBwd k p :=
  rfl

/-! ## §4. The degree-0 case -/

/-- Degree-0 split: both sides are scalars, so `map fst`/`map inl` are mutual
inverses (the second split factor vanishes). -/
noncomputable def extSplitZero :
    ↥(⋀[R]^0 (M × R)) ≃ₗ[R] ↥(⋀[R]^0 M) where
  toLinearMap := exteriorPower.map 0 (LinearMap.fst R M R)
  invFun := exteriorPower.map 0 (LinearMap.inl R M R)
  left_inv z := by
    have hcomp : (exteriorPower.map 0 (LinearMap.inl R M R)).comp
          (exteriorPower.map 0 (LinearMap.fst R M R))
        = LinearMap.id (R := R) (M := ↥(⋀[R]^0 (M × R))) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
      apply Subtype.ext
      simp only [exteriorPower.coe_map, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.ιMulti_zero_apply, map_one]
    exact LinearMap.congr_fun hcomp z
  right_inv y := LinearMap.congr_fun (map_comp_fst_inl 0) y

/-- `extSplitZero` acts by `exteriorPower.map` of `fst`. -/
@[simp]
theorem extSplitZero_apply (z : ↥(⋀[R]^0 (M × R))) :
    extSplitZero z = exteriorPower.map 0 (LinearMap.fst R M R) z :=
  rfl

/-- The inverse of `extSplitZero` acts by `exteriorPower.map` of `inl`. -/
@[simp]
theorem extSplitZero_symm_apply (y : ↥(⋀[R]^0 M)) :
    extSplitZero.symm y = exteriorPower.map 0 (LinearMap.inl R M R) y :=
  rfl

/-- Coercion of `extSplitZero` through the exterior algebra. -/
@[simp]
theorem extSplitZero_coe (z : ↥(⋀[R]^0 (M × R))) :
    ((extSplitZero z : ↥(⋀[R]^0 M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.fst R M R)
        (z : ExteriorAlgebra R (M × R)) :=
  exteriorPower.coe_map _ _

/-! ## §5. Differential matrices -/

/-- Contraction along a split functional commutes with `map inl` on
decomposable wedges: `φ` agrees with `φ'` on `inl`-generators. -/
theorem contract_phi_ιMulti_inl (φ : (M × R) →ₗ[R] R) (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (j : ℕ) (w : Fin j → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R))) φ
        (ExteriorAlgebra.ιMulti R j (LinearMap.inl R M R ∘ w)) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
          (ExteriorAlgebra.ιMulti R j w)) := by
  induction j with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_zero_apply,
      CliffordAlgebra.contractLeft_one, CliffordAlgebra.contractLeft_one,
      map_zero]
  | succ j ih =>
    have h1 := ExteriorAlgebra.ιMulti_succ_apply (R := R) (M := M × R)
      (v := LinearMap.inl R M R ∘ w)
    have h2 := ExteriorAlgebra.ιMulti_succ_apply (R := R) (M := M) (v := w)
    rw [h1, h2, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul]
    have htail : Matrix.vecTail (LinearMap.inl R M R ∘ w) =
        LinearMap.inl R M R ∘ Matrix.vecTail w := rfl
    rw [htail]
    have hphi : φ ((LinearMap.inl R M R ∘ w) 0) = φ' (w 0) := by
      have h := phi_split ((LinearMap.inl R M R ∘ w) 0)
      simpa using h
    rw [hphi, ih, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, ← ExteriorAlgebra.map_apply_ιMulti,
      Function.comp_apply]

/-- Contraction along a split functional commutes with `map inl` (all
elements, via span induction). -/
theorem contract_phi_map_inl (φ : (M × R) →ₗ[R] R) (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (j : ℕ) (x : ↥(⋀[R]^j M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R))) φ
        ((exteriorPower.map j (LinearMap.inl R M R) x : ↥(⋀[R]^j (M × R))) :
          ExteriorAlgebra R (M × R)) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
          (x : ExteriorAlgebra R M)) := by
  have hLR : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R)))
        φ).comp
        ((⋀[R]^j (M × R)).subtype.comp
          (exteriorPower.map j (LinearMap.inl R M R))) =
      (ExteriorAlgebra.map (LinearMap.inl R M R)).toLinearMap.comp
        ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ').comp
          (⋀[R]^j M).subtype) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.coe_subtype, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply]
    exact contract_phi_ιMulti_inl φ φ' r phi_split j v
  exact LinearMap.congr_fun hLR x

/-- Algebra-level form of the commutation lemma. -/
theorem contract_phi_map_inl_alg (φ : (M × R) →ₗ[R] R) (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (j : ℕ) (x : ↥(⋀[R]^j M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (M × R))) φ
        (ExteriorAlgebra.map (LinearMap.inl R M R)
          (x : ExteriorAlgebra R M)) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
          (x : ExteriorAlgebra R M)) := by
  have h := contract_phi_map_inl φ φ' r phi_split j x
  rwa [exteriorPower.coe_map] at h

/-- Contraction kills degree-0 elements (scalars). -/
theorem contract_phi_degree_zero (φ' : M →ₗ[R] R) (y : ↥(⋀[R]^0 M)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
        (y : ExteriorAlgebra R M) = 0 := by
  have hL : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
      φ').comp (⋀[R]^0 M).subtype = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.coe_subtype, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one,
      LinearMap.zero_apply]
  exact LinearMap.congr_fun hL y

/-- Chain differential matrix: under `extSplit`, contraction by `φ` acts as
`(a, b) ↦ (d' a + r • b, -(d' b))`, where `d'` contracts by `φ'`. -/
theorem extSplit_koszulContract (i : ℕ) (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (a : ↥(⋀[R]^(i + 2) M)) (b : ↥(⋀[R]^(i + 1) M)) :
    extSplit i (koszulContract φ (i + 1) ((extSplit (i + 1)).symm (a, b))) =
      (koszulContract φ' (i + 1) a + r • b,
        -(koszulContract φ' i b)) := by
  have hphie : φ ((0, 1) : M × R) = r := by
    have h := phi_split ((0, 1) : M × R)
    simpa using h
  have hCa : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
        (a : ExteriorAlgebra R M) =
        ((koszulContract φ' (i + 1) a : ↥(⋀[R]^(i + 1) M)) :
          ExteriorAlgebra R M) :=
    (koszulContract_apply φ' (i + 1) a).symm
  have hCb : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
        (b : ExteriorAlgebra R M) =
        ((koszulContract φ' i b : ↥(⋀[R]^i M)) : ExteriorAlgebra R M) :=
    (koszulContract_apply φ' i b).symm
  apply Prod.ext
  · apply Subtype.ext
    simp only [extSplit_symm_apply, extSplit_apply, extSplitBwd_coe,
      extSplitFwd_fst_coe, koszulContract_apply, Submodule.coe_add,
      Submodule.coe_smul]
    rw [map_add, contract_phi_map_inl_alg φ φ' r phi_split,
      CliffordAlgebra.contractLeft_ι_mul, hphie,
      contract_phi_map_inl_alg φ φ' r phi_split, map_add, map_sub, map_smul,
      map_mul, map_fst_new, zero_mul, sub_zero, hCa, map_fst_map_inl_coe,
      map_fst_map_inl_coe]
  · apply Subtype.ext
    simp only [extSplit_symm_apply, extSplit_apply, extSplitBwd_coe,
      extSplitFwd_snd_coe, koszulContract_apply, Submodule.coe_neg]
    rw [map_add, contract_phi_map_inl_alg φ φ' r phi_split,
      CliffordAlgebra.contractLeft_ι_mul, hphie,
      contract_phi_map_inl_alg φ φ' r phi_split, map_add, map_sub, map_smul,
      hCa, hCb, contract_snd_map_inl_alg, contract_snd_map_inl_alg,
      contract_snd_wedge_new_alg, smul_zero, zero_sub, zero_add, map_neg,
      map_fst_map_inl_coe]

/-- Chain bottom map: under the splits, `⋀¹ V → ⋀⁰ V` acts as
`(a, b) ↦ d' a + r • b` through `extSplitZero`. -/
theorem extSplit_koszulContract_zero (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (a : ↥(⋀[R]^1 M)) (b : ↥(⋀[R]^0 M)) :
    extSplitZero (koszulContract φ 0 ((extSplit 0).symm (a, b))) =
      koszulContract φ' 0 a + r • b := by
  have hphie : φ ((0, 1) : M × R) = r := by
    have h := phi_split ((0, 1) : M × R)
    simpa using h
  have hCa : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ'
        (a : ExteriorAlgebra R M) =
        ((koszulContract φ' 0 a : ↥(⋀[R]^0 M)) : ExteriorAlgebra R M) :=
    (koszulContract_apply φ' 0 a).symm
  apply Subtype.ext
  simp only [extSplit_symm_apply, extSplitBwd_coe, koszulContract_apply,
    extSplitZero_coe, Submodule.coe_add, Submodule.coe_smul]
  rw [map_add, contract_phi_map_inl_alg φ φ' r phi_split,
    CliffordAlgebra.contractLeft_ι_mul, hphie,
    contract_phi_map_inl_alg φ φ' r phi_split, contract_phi_degree_zero,
    map_zero, mul_zero, sub_zero, map_add, map_smul, hCa,
    map_fst_map_inl_coe, map_fst_map_inl_coe]

/-! ## §6. The `Fin` case -/

/-- Splitting `Fin (n+1) → R` into tail and head, via `Fin.consLinearEquiv`
(swapped to `M × R` form with `prodComm`). -/
noncomputable def finSplitEquiv (n : ℕ) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin n → R) × R :=
  (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm.trans
    (LinearEquiv.prodComm R R (Fin n → R))

/-- The exterior-sum decomposition for `Fin (n+1) → R`, transported along
`finSplitEquiv`: the shape `AugmentedConeStep` consumes. -/
noncomputable def extSplitFin (n k : ℕ) :
    ↥(⋀[R]^(k + 1) (Fin (n + 1) → R)) ≃ₗ[R]
      ↥(⋀[R]^(k + 1) (Fin n → R)) × ↥(⋀[R]^k (Fin n → R)) :=
  (exteriorPower.mapEquiv (finSplitEquiv n) (k + 1)).trans (extSplit k)

/-- `extSplitFin` is `extSplit` after the `finSplitEquiv` transport. -/
@[simp]
theorem extSplitFin_apply (n k : ℕ)
    (z : ↥(⋀[R]^(k + 1) (Fin (n + 1) → R))) :
    extSplitFin n k z =
      extSplit k (exteriorPower.mapEquiv (finSplitEquiv n) (k + 1) z) :=
  rfl

/-- The inverse of `extSplitFin` through the `finSplitEquiv` transport. -/
@[simp]
theorem extSplitFin_symm_apply (n k : ℕ)
    (p : ↥(⋀[R]^(k + 1) (Fin n → R)) × ↥(⋀[R]^k (Fin n → R))) :
    (extSplitFin n k).symm p =
      (exteriorPower.mapEquiv (finSplitEquiv n) (k + 1)).symm
        ((extSplit k).symm p) :=
  rfl

end ExteriorSumDecomposition
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
