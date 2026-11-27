/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Ring

/-!
# Scottish Book Problem 112

The lower unitriangular group over the field with nine elements has a class-preserving
outer automorphism, refuting the claim of Scottish Book Problem 112.
-/

namespace MathlibExt.GroupTheory.ScottishBook112Wanted

/-- The entries in positions `(3, 2)`, `(2, 1)` and `(3, 1)` of a lower unitriangular
matrix of size three. -/
@[ext]
private structure Unitriangular (K : Type*) where
  x : K
  y : K
  z : K

private def Unitriangular.mul {K : Type*} [Ring K] (a b : Unitriangular K) : Unitriangular K :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩

private def Unitriangular.inv {K : Type*} [Ring K] (a : Unitriangular K) : Unitriangular K :=
  ⟨-a.x, -a.y, -a.z + a.x * a.y⟩

private instance unitriangularGroup {K : Type*} [CommRing K] : Group (Unitriangular K) where
  one := ⟨0, 0, 0⟩
  mul := Unitriangular.mul
  inv := Unitriangular.inv
  mul_assoc a b c := by
    change (a.mul b).mul c = a.mul (b.mul c)
    apply Unitriangular.ext <;> dsimp [Unitriangular.mul] <;> ring
  one_mul a := by
    change (Unitriangular.mk 0 0 0).mul a = a
    apply Unitriangular.ext <;> simp [Unitriangular.mul]
  mul_one a := by
    change a.mul ⟨0, 0, 0⟩ = a
    apply Unitriangular.ext <;> simp [Unitriangular.mul]
  inv_mul_cancel a := by
    change a.inv.mul a = ⟨0, 0, 0⟩
    apply Unitriangular.ext <;> dsimp [Unitriangular.mul, Unitriangular.inv] <;> ring

private theorem conjugate_eq {K : Type*} [CommRing K] (g a : Unitriangular K) :
    g * a * g⁻¹ = ⟨a.x, a.y, a.z + (g.x * a.y - a.x * g.y)⟩ := by
  change (g.mul a).mul g.inv = _
  apply Unitriangular.ext <;> dsimp [Unitriangular.mul, Unitriangular.inv] <;> ring

/-- Add a function of the `(3, 2)` entry to the central `(3, 1)` entry. -/
private def centralShift {K : Type*} [CommRing K] (f : K →+ K) : MulAut (Unitriangular K) where
  toFun a := ⟨a.x, a.y, a.z + f a.x⟩
  invFun a := ⟨a.x, a.y, a.z - f a.x⟩
  left_inv a := by
    apply Unitriangular.ext
    · rfl
    · rfl
    · exact add_sub_cancel_right a.z (f a.x)
  right_inv a := by
    apply Unitriangular.ext
    · rfl
    · rfl
    · exact sub_add_cancel a.z (f a.x)
  map_mul' a b := by
    apply Unitriangular.ext
    · rfl
    · rfl
    · change a.z + b.z + a.x * b.y + f (a.x + b.x) =
        a.z + f a.x + (b.z + f b.x) + a.x * b.y
      rw [map_add]
      abel

private theorem centralShift_classPreserving {K : Type*} [Field K] (f : K →+ K)
    (a : Unitriangular K) : ∃ g : Unitriangular K, centralShift f a = g * a * g⁻¹ := by
  by_cases hx : a.x = 0
  · refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    change (⟨a.x, a.y, a.z + f a.x⟩ : Unitriangular K) = a
    rw [hx, map_zero, add_zero, ← hx]
  · refine ⟨⟨0, -(f a.x / a.x), 0⟩, ?_⟩
    rw [conjugate_eq]
    apply Unitriangular.ext
    · rfl
    · rfl
    · change a.z + f a.x = a.z + (0 * a.y - a.x * -(f a.x / a.x))
      rw [zero_mul, zero_sub, mul_neg, neg_neg, mul_div_cancel₀ _ hx]

private theorem centralShift_not_inner {K : Type*} [CommRing K] (f : K →+ K)
    (hf : f 1 = 1) (hn : ∃ t, f t ≠ t) :
    ¬ ∃ g : Unitriangular K, ∀ a, centralShift f a = g * a * g⁻¹ := by
  rintro ⟨g, hg⟩
  have h (t : K) : f t = -(t * g.y) := by
    have heq := congrArg Unitriangular.z (hg ⟨t, 0, 0⟩)
    rw [conjugate_eq] at heq
    change 0 + f t = 0 + (g.x * 0 - t * g.y) at heq
    simpa using heq
  have hy : -g.y = 1 := by
    simpa [hf] using (h 1).symm
  obtain ⟨t, ht⟩ := hn
  exact ht (by rw [h t, ← mul_neg, hy, mul_one])

private theorem exists_frobenius_ne :
    ∃ t : GaloisField 3 2, t ^ 3 ≠ t := by
  by_contra! h
  let F := GaloisField 3 2
  let embed (t : F) : (⊥ : Subfield F) :=
    ⟨t, (Subfield.mem_bot_iff_pow_eq_self F 3).2 (h t)⟩
  have hcard := Nat.card_le_card_of_injective embed (fun _ _ h => congrArg Subtype.val h)
  change Nat.card (GaloisField 3 2) ≤ Nat.card (⊥ : Subfield F) at hcard
  rw [GaloisField.card 3 2 (by decide), Subfield.natCard_bot F 3] at hcard
  exact (by decide : ¬ 3 ^ 2 ≤ 3) hcard

@[expose] public section

/-- **Claim of Scottish Book Problem 112.** The claim that for every group $G$, every
automorphism $\alpha$ of $G$ that sends each element to a conjugate of itself (for each
$x \in G$ there is $g \in G$ with $\alpha(x) = g x g^{-1}$) is inner, that is, there is a
single $g \in G$ with $\alpha(x) = g x g^{-1}$ for all $x \in G$. -/
def ScottishBookProblem112Claim : Prop :=
  ∀ (G : Type*) [Group G] (α : MulAut G),
    (∀ x : G, ∃ g : G, α x = g * x * g⁻¹) →
    ∃ g : G, ∀ x : G, α x = g * x * g⁻¹

/--
**Class-preserving automorphisms need not be inner.** The claim of Scottish Book Problem 112
is false: there are a group $G$ and an automorphism $\alpha$ of $G$ that sends every element
to a conjugate of itself (for each $x \in G$ there is $g \in G$ with $\alpha(x) = g x g^{-1}$)
but is not inner (there is no $g \in G$ with $\alpha(x) = g x g^{-1}$ for all $x \in G$).

Burnside's 1913 example is such a group: for an odd prime $p$, a group of order $p^6$,
isomorphic to the group of $3 \times 3$ lower unitriangular matrices over the field
$\mathbb{F}_{p^2}$, whose group of class-preserving outer automorphisms is nontrivial.

Source: W. Burnside's 1913 example, as summarized in M. K. Yadav,
"Class preserving automorphisms of finite p-groups: A survey",
arXiv:1002.1359, §1 (Burnside constructed a group of order `p ^ 6` with
`Out_c (G) ≠ 1`).
-/
theorem scottishBook112_refuted : ¬ ScottishBookProblem112Claim := by
  intro h
  -- Lift the coefficient field to the universe quantified over by the claim.
  let f := (frobenius (GaloisField 3 2) 3).ulift.toAddMonoidHom
  refine centralShift_not_inner f (by simp [f]) ?_
    (h _ (centralShift f) (centralShift_classPreserving f))
  obtain ⟨t, ht⟩ := exists_frobenius_ne
  exact ⟨ULift.up t, fun heq => ht (congrArg ULift.down heq)⟩

end

end MathlibExt.GroupTheory.ScottishBook112Wanted
