/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspidalType_IsCuspidalOfType_dual.lean`,
`Definitions/Def_CuspidalType_IsCuspidalOfType.lean`
and
`P2M/Sol/S_CuspidalType_IsCuspidalOfType_dual.lean`
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

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.RepresentationTheory.Basic

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp

@[expose] public section

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]

/-- The group `GL₂(𝔽_q)` for prime `q`, as matrices over `ZMod q`. -/
abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)

/-- The projective line over `𝔽_q`. -/
abbrev ProjLine : Type := Projectivization (ZMod q) (Fin 2 → ZMod q)

instance : MulAction (GL2 q) (ProjLine q) :=
  MulAction.compHom (ProjLine q)
    (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod q)).toMonoidHom

instance : NeZero q := ⟨(Fact.out : q.Prime).pos.ne'⟩

instance : Finite (ProjLine q) :=
  Projectivization.finite_of_finite (ZMod q) (Fin 2 → ZMod q)

/-- The unipotent element `[[1, t], [0, 1]]` of `GL₂(𝔽_q)`. -/
def unipotent (t : ZMod q) : GL2 q :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp] theorem unipotent_val (t : ZMod q) :
    (unipotent q t : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, t; 0, 1] := rfl

/-- The scalar matrix attached to a unit of `𝔽_q`. -/
def scalarElem : (ZMod q)ˣ →* GL2 q :=
  Units.map (Matrix.scalar (Fin 2) : ZMod q →+* Matrix (Fin 2) (Fin 2) (ZMod q)).toMonoidHom

/-- The nonsplit torus `𝔽_{q²}ˣ → GL₂(𝔽_q)` from the regular representation. -/
noncomputable def torus : (GaloisField q 2)ˣ →* GL2 q :=
  Units.map
    (MonoidHom.ofClass
      ((LinearMap.toMatrixAlgEquiv
        (Module.finBasisOfFinrankEq (ZMod q) (GaloisField q 2)
          (GaloisField.finrank q two_ne_zero))).toAlgHom.comp
        (Algebra.lmul (ZMod q) (GaloisField q 2))))

variable (k : Type*) [Field k]

/-- The permutation representation of `GL₂(𝔽_q)` on finitely supported
functions on the projective line. -/
noncomputable def ind : Representation k (GL2 q) (ProjLine q →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]

@[simp] theorem ind_single (g : GL2 q) (x : ProjLine q) (r : k) :
    ind q k g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A representation of `GL₂(𝔽_q)` over a field is of cuspidal type `θ` when
it has dimension `q - 1`, no nonzero unipotent-fixed vectors, trivial central
character, and the characteristic polynomial of every nonsplit-torus element
matches that of the permutation representation after dividing by
`(X - θ)(X - θ⁻¹)`. -/
structure IsCuspidalOfType (θ : (GaloisField q 2)ˣ →* Kˣ)
    (ρ : Representation K (GL2 q) V) : Prop where
  finrank_eq : Module.finrank K V = q - 1
  cuspidal : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0
  central : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id
  torus_charpoly : ∀ α : (GaloisField q 2)ˣ,
    LinearMap.charpoly (ρ (torus q α)) * ((X - C ((θ α : Kˣ) : K)) *
      (X - C (((θ α)⁻¹ : Kˣ) : K))) =
      LinearMap.charpoly (ind q K (torus q α))

private theorem charpoly_transpose (f : V →ₗ[K] V) :
    (Module.Dual.transpose (R := K) f).charpoly = f.charpoly := by
  classical
  let b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix (Module.Dual.transpose (R := K) f) b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

private theorem transpose_id :
    Module.Dual.transpose (R := K) (LinearMap.id : V →ₗ[K] V) = LinearMap.id := by
  ext f v
  simp [Module.Dual.transpose_apply]

private theorem charpoly_ind_inv (g : GL2 q) :
    (ind q K g⁻¹).charpoly = (ind q K g).charpoly := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  let b : Module.Basis (ProjLine q) K (ProjLine q →₀ K) := Finsupp.basisSingleOne
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix _ b,
    ← Matrix.charpoly_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, b, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, ind_single, Finsupp.single_apply,
    inv_smul_eq_iff]
  by_cases hij : i = g • j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (Ne.symm hij)]

private theorem unipotent_mul (s t : ZMod q) :
    unipotent q s * unipotent q t = unipotent q (s + t) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem unipotent_inv (t : ZMod q) : (unipotent q t)⁻¹ = unipotent q (-t) :=
  Units.ext rfl

variable {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}

private theorem sum_unipotent_apply_eq_zero (h : IsCuspidalOfType θ ρ) (v : V) :
    (∑ t : ZMod q, ρ (unipotent q t) v) = 0 := by
  apply h.cuspidal
  intro s
  rw [map_sum]
  have hmul : ∀ t : ZMod q, ρ (unipotent q s) (ρ (unipotent q t) v) =
      ρ (unipotent q (s + t)) v := by
    intro t
    rw [← unipotent_mul, map_mul, Module.End.mul_apply]
  simp_rw [hmul]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => rfl)

private theorem dual_eq_zero_of_forall_comp_unipotent (hq : (q : K) ≠ 0)
    (h : IsCuspidalOfType θ ρ) (f : Module.Dual K V)
    (hf : ∀ t : ZMod q, f ∘ₗ ρ (unipotent q t) = f) : f = 0 := by
  ext v
  have hsum : (∑ t : ZMod q, f (ρ (unipotent q t) v)) = (q : K) • f v := by
    have hc : ∀ t : ZMod q, f (ρ (unipotent q t) v) = f v := fun t =>
      LinearMap.congr_fun (hf t) v
    simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, smul_eq_mul]
  have hzero : (q : K) • f v = 0 := by
    rw [← hsum, ← map_sum, sum_unipotent_apply_eq_zero h v, map_zero]
  simpa [hq] using hzero

/-- The dual of a cuspidal-type representation is again of the same cuspidal
type: duality preserves the dimension, kills unipotent-fixed functionals by
averaging over the unipotent group (the only step needing `(q : K) ≠ 0`),
preserves the trivial central character, and preserves the torus
characteristic polynomial since inversion permutes the two roots `θ` and
`θ⁻¹`. -/
public theorem IsCuspidalOfType.dual (hq : (q : K) ≠ 0) (h : IsCuspidalOfType θ ρ) :
    IsCuspidalOfType θ ρ.dual := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Subspace.dual_finrank_eq.trans h.finrank_eq
  · intro f hf
    apply dual_eq_zero_of_forall_comp_unipotent hq h f
    intro t
    have hft := hf (-t)
    rw [Representation.dual_apply, unipotent_inv, neg_neg, Module.Dual.transpose_apply] at hft
    exact hft
  · intro c
    rw [Representation.dual_apply, ← map_inv, h.central, transpose_id]
  · intro α
    rw [Representation.dual_apply, charpoly_transpose]
    have key := h.torus_charpoly α⁻¹
    rw [map_inv θ, inv_inv, map_inv (torus q),
      mul_comm (X - C (((θ α)⁻¹ : Kˣ) : K)) (X - C ((θ α : Kˣ) : K))] at key
    rw [key]
    exact charpoly_ind_inv (torus q α)

end CuspidalType
