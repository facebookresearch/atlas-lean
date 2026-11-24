/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quandle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Virtual racks and quandles

A virtual rack $(R, f)$ is a rack $R$ together with a rack automorphism $f$ of $R$, its virtual
structure. On the dihedral quandle $R_n$, the set $\mathbb{Z}/n\mathbb{Z}$ with
$x \triangleleft y = 2x - y$, the affine maps $T_{a,u} \colon x \mapsto a + u x$ with $u$ a unit
are virtual structures.

## Main definitions

* `MetaMathlibExt.VirtualRackIso`: isomorphism of virtual racks.
* `MetaMathlibExt.dihedralAffinePerm`: the affine permutation $T_{a,u}$ of $R_n$.

## Main statements

* `MetaMathlibExt.dihedral_virtualRackIso_iff`: for $n > 0$, the virtual racks $(R_n, T_{a,u})$
  and $(R_n, T_{b,v})$ are isomorphic if and only if $u = v$ and $b = y a + (1 - u) x$ for some
  $x$ and some unit $y$.

## Implementation notes

For $n > 0$ a map $\psi$ of $\mathbb{Z}/n\mathbb{Z}$ with $\psi(2x - y) = 2\psi(x) - \psi(y)$ is
affine, $\psi(x) = \psi(0) + (\psi(1) - \psi(0)) x$, by induction along $k = 2(k - 1) - (k - 2)$;
for a bijection the slope $\psi(1) - \psi(0)$ is a unit.

## References

* Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer Sequences 28
  (2025), Article 25.8.4, Section 2.2 and Proposition 21.
-/

namespace MetaMathlibExt

@[expose] public section

open Equiv Quandles

/-- **Isomorphism of virtual racks.** Write $x \triangleleft y$ for the operation of a rack. A
virtual rack $(R, f)$ is a rack $R$ together with a rack automorphism $f$ of $R$, its virtual
structure. Let $R_1$ and $R_2$ be racks and let $f_1$ and $f_2$ be permutations of $R_1$ and
$R_2$. Then $(R_1, f_1)$ and $(R_2, f_2)$ are isomorphic when there is a bijection
$\psi \colon R_1 \to R_2$ such that $\psi(x \triangleleft y) = \psi(x) \triangleleft \psi(y)$
for all $x, y \in R_1$ and $\psi(f_1(x)) = f_2(\psi(x))$ for all $x \in R_1$.

The definition does not require $f_1$ and $f_2$ to be rack automorphisms; for virtual racks it
is the usual notion of isomorphism.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
def VirtualRackIso {R₁ R₂ : Type*} [Rack R₁] [Rack R₂] (f₁ : Perm R₁) (f₂ : Perm R₂) : Prop :=
  ∃ ψ : R₁ ≃ R₂, (∀ x y, ψ (x ◃ y) = ψ x ◃ ψ y) ∧ ∀ x, ψ (f₁ x) = f₂ (ψ x)

/-- **Affine permutations of the dihedral quandle.** For a natural number $n$, an element
$a \in \mathbb{Z}/n\mathbb{Z}$ and a unit $u \in (\mathbb{Z}/n\mathbb{Z})^\times$, $T_{a,u}$ is the
affine map $x \mapsto a + u x$ of $\mathbb{Z}/n\mathbb{Z}$, viewed as a permutation of the
dihedral quandle $R_n$ (the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$).

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual structures on the dihedral quandle). -/
def dihedralAffinePerm (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) : Perm (Quandle.Dihedral n) :=
  show Perm (ZMod n) from
  { toFun := fun x => a + (u : ZMod n) * x
    invFun := fun x => ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (x - a)
    left_inv := fun x => by
      simp only [add_sub_cancel_left, Units.inv_mul_cancel_left]
    right_inv := fun x => by
      simp only [Units.mul_inv_cancel_left, add_sub_cancel] }

/-- `T_{a,u}` preserves the dihedral operation `x ◃ y = 2x - y`. -/
private theorem dihedralAffinePerm_act (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) :
    ∀ x y : Quandle.Dihedral n,
      dihedralAffinePerm n a u (x ◃ y) =
        dihedralAffinePerm n a u x ◃ dihedralAffinePerm n a u y := by
  change ∀ x y : ZMod n, _ = _
  intro x y
  change a + (u : ZMod n) * (2 * x - y) = 2 * (a + (u : ZMod n) * x) - (a + (u : ZMod n) * y)
  ring

/-- For `n > 0`, a map `f` of `ZMod n` with `f (2x - y) = 2 f(x) - f(y)` is affine:
`f x = f 0 + (f 1 - f 0) x`. -/
private theorem eq_add_mul_of_map_two_mul_sub {n : ℕ} [NeZero n] (f : ZMod n → ZMod n)
    (hf : ∀ x y, f (2 * x - y) = 2 * f x - f y) (x : ZMod n) :
    f x = f 0 + (f 1 - f 0) * x := by
  have key : ∀ k : ℕ, f k = f 0 + (f 1 - f 0) * k ∧ f (k + 1) = f 0 + (f 1 - f 0) * (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have h := hf ((k : ZMod n) + 1) k
      have e : 2 * ((k : ZMod n) + 1) - k = ((k + 1 : ℕ) : ZMod n) + 1 := by
        push_cast
        ring
      rw [e, ih.2, ih.1] at h
      rw [h]
      push_cast
      ring
  have h := (key x.val).1
  rwa [ZMod.natCast_zmod_val] at h

/-- A surjective affine map `x ↦ c + w x` of `ZMod n` has a unit slope `w`. -/
private theorem isUnit_of_surjective_affine {n : ℕ} (f : ZMod n → ZMod n) (c w : ZMod n)
    (hf : ∀ x, f x = c + w * x) (hs : Function.Surjective f) : IsUnit w := by
  obtain ⟨x, hx⟩ := hs (c + 1)
  rw [hf] at hx
  exact IsUnit.of_mul_eq_one x (by linear_combination hx)

/-- **Isomorphism of affine virtual dihedral quandles.** Let $n > 0$, let $R_n$ be the dihedral
quandle on $\mathbb{Z}/n\mathbb{Z}$ (with $x \triangleleft y = 2x - y$), and for
$a \in \mathbb{Z}/n\mathbb{Z}$ and $u \in (\mathbb{Z}/n\mathbb{Z})^\times$ let $T_{a,u}$ be the
permutation $x \mapsto a + u x$ of $R_n$. For all $a, b \in \mathbb{Z}/n\mathbb{Z}$ and
$u, v \in (\mathbb{Z}/n\mathbb{Z})^\times$, the virtual racks $(R_n, T_{a,u})$ and
$(R_n, T_{b,v})$ are isomorphic if and only if $u = v$ and $b = y a + (1 - u) x$ for some
$x \in \mathbb{Z}/n\mathbb{Z}$ and $y \in (\mathbb{Z}/n\mathbb{Z})^\times$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 21 (`jis-2025-25.8.4-prop-21`). -/
public theorem dihedral_virtualRackIso_iff (n : ℕ) (hn : 0 < n) (a b : ZMod n)
    (u v : (ZMod n)ˣ) :
    VirtualRackIso (dihedralAffinePerm n a u) (dihedralAffinePerm n b v) ↔
      u = v ∧ ∃ x : ZMod n, ∃ y : (ZMod n)ˣ, b = (y : ZMod n) * a + (1 - (u : ZMod n)) * x := by
  have : NeZero n := ⟨hn.ne'⟩
  constructor
  · rintro ⟨ψ, hψ, hcomm⟩
    let f : ZMod n → ZMod n := fun x => ψ x
    have hf : ∀ x y : ZMod n, f (2 * x - y) = 2 * f x - f y := fun x y => hψ x y
    have haff : ∀ x, f x = f 0 + (f 1 - f 0) * x := eq_add_mul_of_map_two_mul_sub f hf
    have hw : IsUnit (f 1 - f 0) :=
      isUnit_of_surjective_affine f (f 0) (f 1 - f 0) haff ψ.surjective
    -- Compare `ψ ∘ T_{a,u}` and `T_{b,v} ∘ ψ` at `0` and at `1`.
    have h0 : f (a + (u : ZMod n) * 0) = b + (v : ZMod n) * f 0 := hcomm (0 : ZMod n)
    have h1 : f (a + (u : ZMod n) * 1) = b + (v : ZMod n) * f 1 := hcomm (1 : ZMod n)
    have e0 := haff (a + (u : ZMod n) * 0)
    have e1 := haff (a + (u : ZMod n) * 1)
    have huv : ((u : ZMod n) - v) * (f 1 - f 0) = 0 := by
      linear_combination h1 - e1 - h0 + e0
    have huv' : (u : ZMod n) = v := sub_eq_zero.mp (hw.mul_left_eq_zero.mp huv)
    refine ⟨Units.ext huv', f 0, hw.unit, ?_⟩
    rw [IsUnit.unit_spec]
    linear_combination e0 - h0 + f 0 * huv'
  · rintro ⟨rfl, x, y, rfl⟩
    refine ⟨dihedralAffinePerm n x y, dihedralAffinePerm_act n x y, ?_⟩
    change ∀ z : ZMod n, _ = _
    intro z
    change x + (y : ZMod n) * (a + (u : ZMod n) * z) =
      ((y : ZMod n) * a + (1 - (u : ZMod n)) * x) + (u : ZMod n) * (x + (y : ZMod n) * z)
    ring

end

end MetaMathlibExt
