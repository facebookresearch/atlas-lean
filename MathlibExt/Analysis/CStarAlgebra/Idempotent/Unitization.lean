/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Idempotent
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Idempotents and projections in nonunital C-star algebras

Every algebraic idempotent in a complex nonunital C-star algebra is
algebraically equivalent to a star projection in the same algebra.  Their
canonical images are conjugate in the unitization.
-/

@[expose] public section

universe u

/-- **Idempotents in a nonunital C*-algebra.** For a nonunital complex C*-algebra `A` and an idempotent
`e ∈ A`, there is a self-adjoint idempotent `p ∈ A` with `e p = p` and `p e = e`. Their images in
the complex unitization of `A` are conjugate by an invertible element. -/
theorem IsIdempotentElem.exists_isStarProjection_isConj_unitization
    {A : Type u} [NonUnitalCStarAlgebra A]
    {e : A} (he : IsIdempotentElem e) :
    ∃ p : A,
      IsStarProjection p ∧
        e * p = p ∧
        p * e = e ∧
        IsConj (e : Unitization ℂ A) (p : Unitization ℂ A) := by
  have heU : IsIdempotentElem (e : Unitization ℂ A) :=
    (Unitization.isIdempotentElem_inr_iff ℂ).mpr he
  obtain ⟨q, hq, hEq, hqE, hconj⟩ :=
    heU.exists_isStarProjection_isConj
  have hqfst : q.fst = 0 := by
    have h := congrArg (fun x : Unitization ℂ A ↦ x.fst) hEq
    simpa only [Unitization.fst_mul, Unitization.fst_inr, zero_mul] using h.symm
  have hqeq : (q.snd : Unitization ℂ A) = q := by
    rw [← Unitization.inl_fst_add_inr_snd_eq q]
    simp [hqfst]
  have hpinr : IsStarProjection (q.snd : Unitization ℂ A) := by
    rw [hqeq]
    exact hq
  have hp : IsStarProjection q.snd :=
    Unitization.isStarProjection_inr_iff.mp hpinr
  have hep : e * q.snd = q.snd := by
    apply Unitization.inr_injective (R := ℂ)
    calc
      ((e * q.snd : A) : Unitization ℂ A) =
          (e : Unitization ℂ A) * (q.snd : Unitization ℂ A) :=
        Unitization.inr_mul ℂ e q.snd
      _ = (e : Unitization ℂ A) * q := by rw [hqeq]
      _ = q := hEq
      _ = (q.snd : Unitization ℂ A) := hqeq.symm
  have hpe : q.snd * e = e := by
    apply Unitization.inr_injective (R := ℂ)
    calc
      ((q.snd * e : A) : Unitization ℂ A) =
          (q.snd : Unitization ℂ A) * (e : Unitization ℂ A) :=
        Unitization.inr_mul ℂ q.snd e
      _ = q * (e : Unitization ℂ A) := by rw [hqeq]
      _ = (e : Unitization ℂ A) := hqE
  have hconj' :
      IsConj (e : Unitization ℂ A) (q.snd : Unitization ℂ A) := by
    rw [hqeq]
    exact hconj
  exact ⟨q.snd, hp, hep, hpe, hconj'⟩
