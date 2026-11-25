/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.SchematicClosure
import Mathlib.Data.ZMod.Basic

@[expose] public section

open scoped TensorProduct

-- Characterization consumer with the original binders: membership unfolds
-- to the defining tensor condition.
example {R F G : Type*} [CommRing R] [Field F] [Algebra R F] [CommRing G]
    [Algebra R G] (B : Subalgebra F (F ⊗[R] G)) (g : G) :
    g ∈ flatClosure B ↔ (1 : F) ⊗ₜ[R] g ∈ B :=
  mem_flatClosure_iff

/-! Concrete closures over `ℤ ⊆ ℚ`. The generic fibre `ℚ ⊗[ℤ] (ℤ × ℤ)` of
`ℤ × ℤ` is read through its two coordinate evaluations to `ℚ`. -/

-- The `ℚ`-algebra map `ℚ ⊗[ℤ] (ℤ × ℤ) → ℚ` induced by a coordinate `π`.
private noncomputable def coordEval (π : ℤ × ℤ →ₐ[ℤ] ℤ) : ℚ ⊗[ℤ] (ℤ × ℤ) →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ ℚ) ((Algebra.ofId ℤ ℚ).comp π)
    fun _ _ => Commute.all _ _

private lemma coordEval_tmul (π : ℤ × ℤ →ₐ[ℤ] ℤ) (q : ℚ) (g : ℤ × ℤ) :
    coordEval π (q ⊗ₜ g) = q * π g := by
  simp [coordEval]

-- If `1 ⊗ g` is the constant `q` of the generic fibre, both coordinates of `g`
-- equal `q`.
private lemma coords_eq_of_algebraMap_eq {g : ℤ × ℤ} {q : ℚ}
    (h : algebraMap ℚ (ℚ ⊗[ℤ] (ℤ × ℤ)) q = (1 : ℚ) ⊗ₜ[ℤ] g) :
    (g.1 : ℚ) = q ∧ (g.2 : ℚ) = q := by
  have h1 := congrArg (coordEval (AlgHom.fst ℤ ℤ ℤ)) h
  have h2 := congrArg (coordEval (AlgHom.snd ℤ ℤ ℤ)) h
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
