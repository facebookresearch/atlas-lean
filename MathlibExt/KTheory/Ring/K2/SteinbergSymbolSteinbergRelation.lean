/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol
import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations

/-! # Steinberg relation for the canonical torus cocycle

We prove `h(u)h(v)=h(uv)` when `u+v=1` via the rank-one word calculation
`w(u)w(-1)w(v)=w(uv)` (Weibel K-book Lemma III.5.10.2),
hence the cocycle `c(u,v)=h(u)h(v)h(uv)^{-1}` is trivial and `{a,1-a}=1`.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory.StableSteinberg

variable {F : Type u} [Field F]

private lemma weyl_mul_x10_one (u : Fˣ) :
    weyl (R := F) 0 1 (by omega) u * x (R := F) 1 0 (by omega) (1 : F) =
      x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
        weyl (R := F) 0 1 (by omega) u := by
  have hconj :=
    weyl_conj_x_ji (R := F) (i := 0) (j := 1) (by omega) (u := u) (a := (1 : F))
  rw [show -((u : F) * (1 : F) * (u : F)) = -((u : F) * (u : F)) from by ring] at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj

private lemma x10_one_mul_weyl (u : Fˣ) :
    x (R := F) 1 0 (by omega) (1 : F) * weyl (R := F) 0 1 (by omega) u =
      weyl (R := F) 0 1 (by omega) u * x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) := by
  have hconj :=
    weyl_conj_x_ji (R := F) (i := 0) (j := 1) (by omega) (u := (-u)) (a := (1 : F))
  have hcoeff : -(((-u : Fˣ) : F) * (1 : F) * ((-u : Fˣ) : F)) = -((u : F) * (u : F)) := by
    have : ((-u : Fˣ) : F) = -(u : F) := by simp
    rw [this]; ring
  rw [hcoeff, weyl_neg_eq_inv] at hconj
  have h : (weyl (R := F) 0 1 (by omega) u)⁻¹ * (x (R := F) 1 0 (by omega) (1 : F) *
      weyl (R := F) 0 1 (by omega) u) =
      x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) := by
    rw [← mul_assoc]; exact hconj
  exact inv_mul_eq_iff_eq_mul.mp h

private lemma weyl_01_neg_one_eq_reverse :
    weyl (R := F) 0 1 (by omega) (-1 : Fˣ) =
      x (R := F) 1 0 (by omega) (1 : F) *
        x (R := F) 0 1 (by omega) (-1 : F) *
          x (R := F) 1 0 (by omega) (1 : F) := by
  let a := x (R := F) 0 1 (by omega) (-1 : F)
  let b := x (R := F) 1 0 (by omega) (1 : F)
  have hw_def : weyl (R := F) 0 1 (by omega) (-1 : Fˣ) = a * b * a := by
    simp [weyl, a, b]
  have h_move : weyl (R := F) 0 1 (by omega) (-1 : Fˣ) * b =
        a * weyl (R := F) 0 1 (by omega) (-1 : Fˣ) := by
    have h := weyl_mul_x10_one (F := F) (-1 : Fˣ)
    rw [show -(((-1 : Fˣ) : F) * ((-1 : Fˣ) : F)) = (-1 : F) from by simp] at h
    exact h
  have h_eq : a * b * a * b = a * a * b * a := by
    calc a * b * a * b = weyl (R := F) 0 1 (by omega) (-1 : Fˣ) * b := by rw [← hw_def]
      _ = a * weyl (R := F) 0 1 (by omega) (-1 : Fˣ) := h_move
      _ = a * (a * b * a) := by rw [← hw_def]
      _ = a * a * b * a := by simp only [mul_assoc]
  have h_cancel : b * a * b = a * b * a := by
    apply mul_left_cancel (a := a)
    calc a * (b * a * b) = a * b * a * b := by simp only [mul_assoc]
      _ = a * a * b * a := h_eq
      _ = a * (a * b * a) := by simp only [mul_assoc]
  calc weyl (R := F) 0 1 (by omega) (-1 : Fˣ)
      = a * b * a := hw_def
    _ = b * a * b := h_cancel.symm
    _ = x (R := F) 1 0 (by omega) (1 : F) *
          x (R := F) 0 1 (by omega) (-1 : F) *
            x (R := F) 1 0 (by omega) (1 : F) := by rfl

private theorem weyl_mul_weyl_of_add_eq_one {u v : Fˣ}
    (hadd : (u : F) + (v : F) = 1) :
    weyl (R := F) 0 1 (by omega) u *
      weyl (R := F) 0 1 (by omega) (-1 : Fˣ) *
        weyl (R := F) 0 1 (by omega) v =
      weyl (R := F) 0 1 (by omega) (u * v) := by
  have h_coeff1 : -((u : F) * (u : F)) + (u : F) = (u : F) * (v : F) := by
    rw [show (v : F) = 1 - (u : F) from by
      calc (v : F) = (u : F) + (v : F) - (u : F) := by ring
        _ = 1 - (u : F) := by rw [hadd]]; ring
  have h_coeff2 : (v : F) + -((v : F) * (v : F)) = (u : F) * (v : F) := by
    rw [show (u : F) = 1 - (v : F) from by
      calc (u : F) = (u : F) + (v : F) - (v : F) := by ring
        _ = 1 - (v : F) := by rw [hadd]]; ring
  have h_inv_add :
      (-((u : F)⁻¹) : F) + (-((v : F)⁻¹) : F) =
        -(((u * v : Fˣ) : F)⁻¹ : F) := by
    have hu : (u : F) ≠ 0 := Units.ne_zero u
    have hv : (v : F) ≠ 0 := Units.ne_zero v
    rw [show (((u * v : Fˣ) : F)⁻¹ : F) = ((u : F) * (v : F))⁻¹ from by
      rw [Units.val_mul]]
    calc (-((u : F)⁻¹) : F) + (-((v : F)⁻¹) : F)
        = -(((u : F)⁻¹ + (v : F)⁻¹ : F)) := by ring
      _ = -(((u : F) + (v : F)) / ((u : F) * (v : F)) : F) := by
          rw [inv_add_inv hu hv]
      _ = -(1 / ((u : F) * (v : F)) : F) := by rw [hadd]
      _ = -(((u : F) * (v : F))⁻¹ : F) := by rw [one_div]
  calc weyl (R := F) 0 1 (by omega) u *
        weyl (R := F) 0 1 (by omega) (-1 : Fˣ) *
          weyl (R := F) 0 1 (by omega) v
      = weyl (R := F) 0 1 (by omega) u *
          (x (R := F) 1 0 (by omega) (1 : F) *
            x (R := F) 0 1 (by omega) (-1 : F) *
              x (R := F) 1 0 (by omega) (1 : F)) *
            weyl (R := F) 0 1 (by omega) v := by
        rw [weyl_01_neg_one_eq_reverse]
    _ = (weyl (R := F) 0 1 (by omega) u * x (R := F) 1 0 (by omega) (1 : F)) *
          x (R := F) 0 1 (by omega) (-1 : F) *
            (x (R := F) 1 0 (by omega) (1 : F) * weyl (R := F) 0 1 (by omega) v) := by
        simp only [mul_assoc]
    _ = (x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
            weyl (R := F) 0 1 (by omega) u) *
          x (R := F) 0 1 (by omega) (-1 : F) *
            (weyl (R := F) 0 1 (by omega) v *
              x (R := F) 0 1 (by omega) (-((v : F) * (v : F)))) := by
        rw [weyl_mul_x10_one, x10_one_mul_weyl]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (weyl (R := F) 0 1 (by omega) u *
            x (R := F) 0 1 (by omega) (-1 : F) *
              weyl (R := F) 0 1 (by omega) v) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        simp only [mul_assoc]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            x (R := F) 1 0 (by omega) (-((u : F)⁻¹)) *
              x (R := F) 0 1 (by omega) ((u : F)) *
                x (R := F) 0 1 (by omega) (-1 : F) *
                  (x (R := F) 0 1 (by omega) ((v : F)) *
                    x (R := F) 1 0 (by omega) (-((v : F)⁻¹)) *
                      x (R := F) 0 1 (by omega) ((v : F)))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        simp only [weyl, Units.val_inv_eq_inv_val]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            x (R := F) 1 0 (by omega) (-((u : F)⁻¹)) *
              (x (R := F) 0 1 (by omega) ((u : F)) *
                x (R := F) 0 1 (by omega) (-1 : F) *
                  x (R := F) 0 1 (by omega) ((v : F))) *
                x (R := F) 1 0 (by omega) (-((v : F)⁻¹)) *
                  x (R := F) 0 1 (by omega) ((v : F))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        simp only [mul_assoc]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            x (R := F) 1 0 (by omega) (-((u : F)⁻¹)) *
              x (R := F) 0 1 (by omega) (0 : F) *
                x (R := F) 1 0 (by omega) (-((v : F)⁻¹)) *
                  x (R := F) 0 1 (by omega) ((v : F))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        have h7 : x (R := F) 0 1 (by omega) ((u : F)) *
              x (R := F) 0 1 (by omega) (-1 : F) *
                x (R := F) 0 1 (by omega) ((v : F)) =
              x (R := F) 0 1 (by omega) (0 : F) := by
          rw [x_add, x_add]
          have : (u : F) + (-1 : F) + (v : F) = 0 := by
            calc (u : F) + (-1) + (v : F)
                = (u : F) + (v : F) - 1 := by ring
              _ = 0 := by rw [hadd, sub_self]
          rw [this]
        rw [h7]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            (x (R := F) 1 0 (by omega) (-((u : F)⁻¹)) *
              x (R := F) 1 0 (by omega) (-((v : F)⁻¹))) *
              x (R := F) 0 1 (by omega) ((v : F))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        simp only [mul_assoc, x_zero, mul_one]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            x (R := F) 1 0 (by omega) (-((u : F)⁻¹) + (-((v : F)⁻¹))) *
              x (R := F) 0 1 (by omega) ((v : F))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        rw [← x_add (i := 1) (j := 0)]
    _ = x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
          (x (R := F) 0 1 (by omega) ((u : F)) *
            x (R := F) 1 0 (by omega) (-(((u * v : Fˣ) : F)⁻¹)) *
              x (R := F) 0 1 (by omega) ((v : F))) *
            x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) := by
        rw [h_inv_add]
    _ = (x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
            x (R := F) 0 1 (by omega) ((u : F))) *
          x (R := F) 1 0 (by omega) (-(((u * v : Fˣ) : F)⁻¹)) *
            (x (R := F) 0 1 (by omega) ((v : F)) *
              x (R := F) 0 1 (by omega) (-((v : F) * (v : F)))) := by
        simp only [mul_assoc]
    _ = x (R := F) 0 1 (by omega) ((u : F) * (v : F)) *
          x (R := F) 1 0 (by omega) (-(((u * v : Fˣ) : F)⁻¹)) *
            x (R := F) 0 1 (by omega) ((u : F) * (v : F)) := by
        have h8 : x (R := F) 0 1 (by omega) (-((u : F) * (u : F))) *
              x (R := F) 0 1 (by omega) ((u : F)) =
              x (R := F) 0 1 (by omega) ((u : F) * (v : F)) := by
          rw [x_add, h_coeff1]
        have h9 : x (R := F) 0 1 (by omega) ((v : F)) *
              x (R := F) 0 1 (by omega) (-((v : F) * (v : F))) =
              x (R := F) 0 1 (by omega) ((u : F) * (v : F)) := by
          rw [x_add, h_coeff2]
        rw [h8, h9]
    _ = weyl (R := F) 0 1 (by omega) (u * v) := by
        simp only [weyl, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem torusCocycle_eq_one_of_add_eq_one {u v : Fˣ}
    (hadd : (u : F) + (v : F) = 1) :
    torusCocycle (F := F) u v = 1 := by
  have htorus : torus (R := F) 0 1 (by omega) u *
      torus (R := F) 0 1 (by omega) v =
      torus (R := F) 0 1 (by omega) (u * v) := by
    have hw := weyl_mul_weyl_of_add_eq_one hadd
    calc torus (R := F) 0 1 (by omega) u * torus (R := F) 0 1 (by omega) v
        = (weyl (R := F) 0 1 (by omega) u * weyl (R := F) 0 1 (by omega) (-1 : Fˣ)) *
            (weyl (R := F) 0 1 (by omega) v * weyl (R := F) 0 1 (by omega) (-1 : Fˣ)) := by
          simp only [torus]
        _ = weyl (R := F) 0 1 (by omega) u *
            weyl (R := F) 0 1 (by omega) (-1 : Fˣ) *
              weyl (R := F) 0 1 (by omega) v *
                weyl (R := F) 0 1 (by omega) (-1 : Fˣ) := by
          simp only [mul_assoc]
        _ = weyl (R := F) 0 1 (by omega) (u * v) *
            weyl (R := F) 0 1 (by omega) (-1 : Fˣ) := by rw [hw]
        _ = torus (R := F) 0 1 (by omega) (u * v) := by
          simp only [torus]
  exact mul_inv_eq_iff_eq_mul.mpr htorus

/-- Steinberg relation for the torus cocycle: `c(a,1-a)=1`. -/
theorem torusCocycle_steinberg (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    torusCocycle
      (Units.mk0 a ha0)
      (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 1 := by
  exact torusCocycle_eq_one_of_add_eq_one (by simp only [Units.val_mk0]; ring)

end AlgebraicKTheory.StableSteinberg

namespace AlgebraicKTheory.K2

variable {F : Type u} [Field F]

/-- Steinberg relation for the `K₂` symbol: `{a,1-a}=1`. -/
theorem steinbergSymbol_steinberg (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    steinbergSymbol
      (Units.mk0 a ha0)
      (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 1 := by
  apply K2.ext
  simp only [inclusion_steinbergSymbol, map_one]
  exact StableSteinberg.torusCocycle_steinberg a ha0 ha1

end AlgebraicKTheory.K2

end
