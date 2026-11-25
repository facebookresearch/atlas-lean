/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quandle
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Automorphisms of racks and conjugation quandles
-/

namespace MetaMathlibExt

open Equiv Quandles

/-- **Automorphism group of a rack.** For a rack $R$ with operation $\triangleleft$, the
automorphism group $\operatorname{Aut} R$ is the subgroup of the group of permutations of $R$
consisting of the permutations $f$ with $f(x \triangleleft y) = f(x) \triangleleft f(y)$ for all
$x, y \in R$.

Here $x \triangleleft y$ is the paper's $s_x(y)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (rack homomorphisms and `Aut R`). -/
@[expose] public def rackAut (R : Type*) [Rack R] : Subgroup (Perm R) where
  carrier := {f | ∀ x y, f (x ◃ y) = f x ◃ f y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg x y
    simp only [Perm.mul_apply, hg x y, hf (g x) (g y)]
  inv_mem' := by
    intro f hf x y
    apply f.injective
    rw [hf (f⁻¹ x) (f⁻¹ y)]
    simp

/-- **Trivial center and automorphisms of the conjugation quandle.** For a group $G$, let
$\operatorname{Conj}(G)$ be the conjugation quandle on $G$, with $x \triangleleft y = x y x^{-1}$.
Then $G$ has trivial center if and only if the permutations of $G$ that are group automorphisms
are exactly the rack automorphisms of $\operatorname{Conj}(G)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Lemma 17 (`jis-2025-25.8.4-lem-17`), quoting Bardakov,
Nasybullov, and Singh, Corollary 2. -/
public theorem center_eq_bot_iff_mulAut_eq_rackAut_conj (G : Type*) [Group G] :
    Subgroup.center G = ⊥ ↔
      (MulAut.toPerm (M := G)).range = rackAut (Quandle.Conj G) := by
  have conj_eq_one_iff {z : G} : MulAut.conj z = 1 ↔ z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hz x
      exact (mul_inv_eq_iff_eq_mul.mp (DFunLike.congr_fun hz x)).symm
    · intro hz
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply, ← hz x, mul_inv_cancel_right]
  constructor
  · intro h
    -- Faithful conjugation recovers the product of two elements from their actions.
    have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← h]
      exact Subgroup.ext fun _ => conj_eq_one_iff
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      intro x y
      exact (Quandle.Conj.map f.toMonoidHom).map_act
    · intro f hf
      have hconj (a b : G) : f (MulAut.conj a b) = MulAut.conj (f a) (f b) := hf a b
      refine ⟨{ f with map_mul' := ?_ }, rfl⟩
      intro a b
      apply hinj
      apply MulEquiv.ext
      intro w
      obtain ⟨x, rfl⟩ := f.surjective w
      calc
        MulAut.conj (f (a * b)) (f x) = f (MulAut.conj (a * b) x) := (hconj (a * b) x).symm
        _ = MulAut.conj (f a * f b) (f x) := by
          simp only [map_mul, MulAut.mul_apply, hconj]
  · intro h
    apply le_bot_iff.mp
    intro z hz
    -- Translation by a central element preserves conjugation, but must fix `1`
    -- if it comes from a group automorphism.
    have htrans : Equiv.mulLeft z ∈ rackAut (Quandle.Conj G) := by
      intro x y
      change z * MulAut.conj x y = MulAut.conj (z * x) (z * y)
      have hconj : MulAut.conj (z * x) = MulAut.conj x := by
        rw [map_mul, conj_eq_one_iff.mpr hz, one_mul]
      rw [hconj, map_mul, MulAut.conj_apply x z, Subgroup.mem_center_iff.mp hz x,
        mul_inv_cancel_right]
    obtain ⟨f, hf⟩ := h.ge htrans
    have h_one : f 1 = z * 1 := Equiv.congr_fun hf 1
    simpa only [Subgroup.mem_bot, mul_one, map_one] using h_one.symm

end MetaMathlibExt
