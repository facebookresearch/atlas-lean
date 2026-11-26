/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.FlatClosure
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

@[expose] public section

open scoped TensorProduct

-- Characterization consumer with the original binders: membership unfolds
-- to the defining tensor condition.
example {R F G : Type*} [CommRing R] [Field F] [Algebra R F] [CommRing G]
    [Algebra R G] (B : Subalgebra F (F ⊗[R] G)) (g : G) :
    g ∈ flatClosure B ↔ (1 : F) ⊗ₜ[R] g ∈ B :=
  mem_flatClosure_iff

/-! Concrete closures over `ℤ`. The base change `K ⊗[ℤ] (ℤ × ℤ)` of `ℤ × ℤ` to a field `K`
is read through its two coordinate evaluations to `K`; for `K = ℚ` it is the generic fibre. -/

-- The `K`-algebra map `K ⊗[ℤ] (ℤ × ℤ) → K` induced by a coordinate `π`.
private noncomputable def coordEval (K : Type) [Field K] (π : ℤ × ℤ →ₐ[ℤ] ℤ) :
    K ⊗[ℤ] (ℤ × ℤ) →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId ℤ K).comp π)
    fun _ _ => Commute.all _ _

private lemma coordEval_tmul {K : Type} [Field K] (π : ℤ × ℤ →ₐ[ℤ] ℤ) (q : K)
    (g : ℤ × ℤ) : coordEval K π (q ⊗ₜ g) = q * π g := by
  simp [coordEval]

-- If `1 ⊗ g` is the constant `q` of the base change to `K`, both coordinates of
-- `g` equal `q` in `K`.
private lemma coords_eq_of_algebraMap_eq {K : Type} [Field K] {g : ℤ × ℤ} {q : K}
    (h : algebraMap K (K ⊗[ℤ] (ℤ × ℤ)) q = (1 : K) ⊗ₜ[ℤ] g) :
    (g.1 : K) = q ∧ (g.2 : K) = q := by
  have h1 := congrArg (coordEval K (AlgHom.fst ℤ ℤ ℤ)) h
  have h2 := congrArg (coordEval K (AlgHom.snd ℤ ℤ ℤ)) h
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, coordEval_tmul,
    AlgHom.fst_apply, AlgHom.snd_apply, one_mul] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

-- The closure of the constants `⊥` of the generic fibre is the diagonal, i.e.
-- the constants `⊥` of `ℤ × ℤ`.
example : flatClosure (⊥ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) = ⊥ := by
  refine le_antisymm (fun g hg => ?_) bot_le
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp (mem_flatClosure_iff.mp hg)
  obtain ⟨h1, h2⟩ := coords_eq_of_algebraMap_eq hq
  have h : g.2 = g.1 := by exact_mod_cast h2.trans h1.symm
  exact Algebra.mem_bot.mpr ⟨g.1, Prod.ext (by simp) (by simp [h])⟩

-- `(1, 0)` lies in the closure of `⊤` but not in that of `⊥`: the closure
-- depends on `B`.
example : ((1, 0) : ℤ × ℤ) ∉ flatClosure (⊥ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) := by
  intro h
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp (mem_flatClosure_iff.mp h)
  obtain ⟨h1, h2⟩ := coords_eq_of_algebraMap_eq hq
  norm_num at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

example : ((1, 0) : ℤ × ℤ) ∈ flatClosure (⊤ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) :=
  mem_flatClosure_iff.mpr Algebra.mem_top

example : flatClosure (⊤ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_flatClosure_iff.mpr Algebra.mem_top

-- Torsion dies in the generic fibre: the 2-torsion element `(0, 1)` of
-- `ℤ × ZMod 2` lies in the closure of `⊥`.
private lemma zero_one_mem_flatClosure_bot :
    ((0, 1) : ℤ × ZMod 2) ∈ flatClosure (⊥ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ZMod 2))) := by
  rw [mem_flatClosure_iff]
  have h : (1 : ℚ) ⊗ₜ[ℤ] ((0, 1) : ℤ × ZMod 2) = 0 := by
    calc (1 : ℚ) ⊗ₜ[ℤ] ((0, 1) : ℤ × ZMod 2)
        = ((2 : ℤ) • (2⁻¹ : ℚ)) ⊗ₜ[ℤ] ((0, 1) : ℤ × ZMod 2) := by norm_num
      _ = (2⁻¹ : ℚ) ⊗ₜ[ℤ] ((2 : ℤ) • ((0, 1) : ℤ × ZMod 2)) := TensorProduct.smul_tmul _ _ _
      _ = 0 := by
        rw [show (2 : ℤ) • ((0, 1) : ℤ × ZMod 2) = 0 by decide, TensorProduct.tmul_zero]
  rw [h]
  exact zero_mem _

-- So, unlike for `ℤ × ℤ`, the closure of `⊥` is not `⊥`: `(0, 1)` is not a
-- constant `(n, n)` of `ℤ × ZMod 2`.
example : flatClosure (⊥ : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ZMod 2))) ≠ ⊥ := by
  intro h
  obtain ⟨n, hn⟩ := Algebra.mem_bot.mp (h ▸ zero_one_mem_flatClosure_bot)
  have h1 : n = 0 := by simpa using congrArg Prod.fst hn
  have h2 := congrArg Prod.snd hn
  simp [h1] at h2

-- The closure is a preimage, not a saturation: over `F = ZMod 2` the element
-- `1 ⊗ (2, 0) = (2 • 1) ⊗ (1, 0)` is `0`, so `(2, 0) = 2 • (1, 0)` lies in the
-- closure of `⊥` while `(1, 0)` does not.
example :
    ((2, 0) : ℤ × ℤ) ∈ flatClosure (⊥ : Subalgebra (ZMod 2) (ZMod 2 ⊗[ℤ] (ℤ × ℤ))) := by
  rw [mem_flatClosure_iff]
  have h : (1 : ZMod 2) ⊗ₜ[ℤ] ((2, 0) : ℤ × ℤ) = 0 := by
    calc (1 : ZMod 2) ⊗ₜ[ℤ] ((2, 0) : ℤ × ℤ)
        = (1 : ZMod 2) ⊗ₜ[ℤ] ((2 : ℤ) • ((1, 0) : ℤ × ℤ)) := by norm_num
      _ = ((2 : ℤ) • (1 : ZMod 2)) ⊗ₜ[ℤ] ((1, 0) : ℤ × ℤ) := (TensorProduct.smul_tmul _ _ _).symm
      _ = 0 := by rw [show (2 : ℤ) • (1 : ZMod 2) = 0 by decide, TensorProduct.zero_tmul]
  rw [h]
  exact zero_mem _

example :
    ((1, 0) : ℤ × ℤ) ∉ flatClosure (⊥ : Subalgebra (ZMod 2) (ZMod 2 ⊗[ℤ] (ℤ × ℤ))) := by
  intro h
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp (mem_flatClosure_iff.mp h)
  obtain ⟨h1, h2⟩ := coords_eq_of_algebraMap_eq hq
  simp only [Int.cast_one, Int.cast_zero] at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

-- Over the PID `ℤ`, the finite, free and flat conclusions apply to closures in
-- the finite torsion-free algebra `ℤ × ℤ`.
example (B : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) : Module.Finite ℤ (flatClosure B) :=
  flatClosure_finite B

example (B : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) : Module.Free ℤ (flatClosure B) :=
  flatClosure_free B

example (B : Subalgebra ℚ (ℚ ⊗[ℤ] (ℤ × ℤ))) : Module.Flat ℤ (flatClosure B) :=
  flatClosure_flat B

-- Monotonicity consumer.
example {R F G : Type*} [CommRing R] [Field F] [Algebra R F] [CommRing G]
    [Algebra R G] {B B' : Subalgebra F (F ⊗[R] G)} (h : B ≤ B') :
    flatClosure B ≤ flatClosure B' :=
  flatClosure_mono h
