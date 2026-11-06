/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Concrete coordinate reduction for potential Y₅₅₅ generators in a wreath product.
The factor M is arbitrary: in the application it must be the actual group G.
No generator family satisfying the source relations is assumed to exist here.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555Parity

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {M : Type*} [Group M]

/-- Embed the two independently specified factors into the actual wreath base. -/
def y555WreathBase : M × M →* M ≀ᵣ WreathParity where
  toFun p := ⟨fun x => if x = 1 then p.1 else p.2, 1⟩
  map_one' := by ext x <;> simp
  map_mul' p q := by
    apply RegularWreathProduct.ext
    · funext x
      rcases wreathParity_cases x with rfl | rfl <;>
        simp [RegularWreathProduct.mul_left, wreathFlip,
          show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide]
    · rfl

/-- Each outer involution has this form: entries m and m⁻¹, then factor swap. -/
def y555WreathReflection (m : M) : M ≀ᵣ WreathParity :=
  ⟨fun x => if x = 1 then m else m⁻¹, wreathFlip⟩

@[simp] theorem y555WreathReflection_one :
    y555WreathReflection (1 : M) = wreathSwap M := by
  ext x <;> simp [y555WreathReflection, wreathSwap]

@[simp] theorem y555WreathReflection_right (m : M) :
    (y555WreathReflection m).right = wreathFlip := rfl

/-- Multiplication of two proposed generators becomes a pair of factor words. -/
theorem y555WreathReflection_mul (m n : M) :
    y555WreathReflection m * y555WreathReflection n =
      y555WreathBase (m * n⁻¹, m⁻¹ * n) := by
  apply RegularWreathProduct.ext
  · funext x
    rcases wreathParity_cases x with rfl | rfl <;>
      simp [y555WreathReflection, y555WreathBase, wreathFlip,
        show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide]
  · exact wreathFlip_sq

@[simp] theorem y555WreathReflection_sq (m : M) :
    y555WreathReflection m ^ 2 = 1 := by
  rw [pow_two, y555WreathReflection_mul, mul_inv_cancel, inv_mul_cancel]
  exact y555WreathBase.map_one

/-- The two factor entries can be tested independently. -/
theorem y555WreathBase_eq_one (p : M × M) :
    y555WreathBase p = 1 ↔ p.1 = 1 ∧ p.2 = 1 := by
  constructor
  · intro h
    constructor
    · exact congrArg (fun w : M ≀ᵣ WreathParity => w.left 1) h
    · simpa [y555WreathBase, wreathFlip,
        show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide] using
        congrArg (fun w : M ≀ᵣ WreathParity => w.left wreathFlip) h
  · rintro ⟨h, k⟩
    have hp : p = 1 := Prod.ext h k
    rw [hp, map_one]

/-- All 120 pairwise Coxeter relation checks reduce to one factor each.
This statement is an exact equivalence, valid in the actual group M. -/
theorem y555WreathReflection_mul_pow (m n : M) (k : ℕ) :
    (y555WreathReflection m * y555WreathReflection n) ^ k = 1 ↔
      (m * n⁻¹) ^ k = 1 := by
  rw [y555WreathReflection_mul, ← map_pow, y555WreathBase_eq_one]
  change (m * n⁻¹) ^ k = 1 ∧ (m⁻¹ * n) ^ k = 1 ↔ (m * n⁻¹) ^ k = 1
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    have he : m⁻¹ * n = m⁻¹ * (m * n⁻¹)⁻¹ * (m⁻¹)⁻¹ := by group
    rw [he, conj_pow, inv_pow, h]
    simp

/-- Normalize the image of an arbitrary outer involution to the same concrete
parameterization. -/
theorem y555WreathReflection_of_outer (g : M ≀ᵣ WreathParity)
    (hg : g * g = 1) (hp : g.right = wreathFlip) :
    g = y555WreathReflection (g.left 1) := by
  have hl : g.left 1 * g.left wreathFlip = 1 := by
    have h := congrArg (fun w : M ≀ᵣ WreathParity => w.left 1) hg
    simpa only [RegularWreathProduct.mul_left, Pi.mul_apply, hp,
      wreathFlip_inv, mul_one, RegularWreathProduct.one_left, Pi.one_apply] using h
  have hi : g.left wreathFlip = (g.left 1)⁻¹ := eq_inv_of_mul_eq_one_right hl
  apply RegularWreathProduct.ext
  · funext x
    rcases wreathParity_cases x with rfl | rfl
    · simp [y555WreathReflection]
    · simpa [y555WreathReflection, wreathFlip,
        show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide] using hi
  · exact hp

/-- An even power of any element in the outer coset reduces to one factor word. -/
theorem y555Wreath_outer_even_pow (g : M ≀ᵣ WreathParity)
    (hp : g.right = wreathFlip) (k : ℕ) :
    g ^ (2 * k) = 1 ↔ (g.left 1 * g.left wreathFlip) ^ k = 1 := by
  have hs : g ^ 2 = y555WreathBase
      (g.left 1 * g.left wreathFlip, g.left wreathFlip * g.left 1) := by
    rw [pow_two]
    apply RegularWreathProduct.ext
    · funext x
      rcases wreathParity_cases x with rfl | rfl <;>
        simp [RegularWreathProduct.mul_left, hp, y555WreathBase, wreathFlip_inv, wreathFlip_sq,
          show wreathFlip ≠ 1 by decide]
    · change g.right * g.right = 1
      rw [hp]
      exact wreathFlip_sq
  rw [pow_mul, hs, ← map_pow, y555WreathBase_eq_one]
  change (g.left 1 * g.left wreathFlip) ^ k = 1 ∧
    (g.left wreathFlip * g.left 1) ^ k = 1 ↔ _
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    have he : g.left wreathFlip * g.left 1 =
        (g.left 1)⁻¹ * (g.left 1 * g.left wreathFlip) * ((g.left 1)⁻¹)⁻¹ := by group
    rw [he, conj_pow, h]
    simp

/-- First factor word of the nine-letter spider when the central parameter is one. -/
def y555SpiderFirst (m : Y555Vertex → M) : M :=
  (m (some (0, 0)))⁻¹ * m (some (0, 1)) *
    m (some (1, 0)) * (m (some (1, 1)))⁻¹ *
    (m (some (2, 0)))⁻¹ * m (some (2, 1))

/-- Second factor word of the same spider. -/
def y555SpiderSecond (m : Y555Vertex → M) : M :=
  m (some (0, 0)) * (m (some (0, 1)))⁻¹ *
    (m (some (1, 0)))⁻¹ * m (some (1, 1)) *
    m (some (2, 0)) * (m (some (2, 1)))⁻¹

/-- Evaluate the primary-source spider word on the proposed outer generators. -/
def y555WreathSpider (m : Y555Vertex → M) : M ≀ᵣ WreathParity :=
  FreeGroup.lift (fun v => y555WreathReflection (m v)) y555Spider

/-- The spider is in the outer coset, since it has nine letters. -/
@[simp] theorem y555WreathSpider_right (m : Y555Vertex → M) :
    (y555WreathSpider m).right = wreathFlip := by
  simp [y555WreathSpider, y555Spider, y555WreathReflection,
    wreathFlip_sq, mul_assoc, RegularWreathProduct.mul_right]

/-- Exact first-coordinate evaluation, valid for arbitrary factor elements. -/
theorem y555WreathSpider_first (m : Y555Vertex → M) (hm : m none = 1) :
    (y555WreathSpider m).left 1 = y555SpiderFirst m := by
  simp [y555WreathSpider, y555Spider, y555WreathReflection, hm,
    RegularWreathProduct.mul_left, wreathFlip_inv, wreathFlip_sq, mul_assoc, y555SpiderFirst,
    show wreathFlip ≠ 1 by decide]

/-- Exact second-coordinate evaluation. -/
theorem y555WreathSpider_second (m : Y555Vertex → M) (hm : m none = 1) :
    (y555WreathSpider m).left wreathFlip = y555SpiderSecond m := by
  simp [y555WreathSpider, y555Spider, y555WreathReflection, hm,
    RegularWreathProduct.mul_left, wreathFlip_inv, wreathFlip_sq, mul_assoc, y555SpiderSecond,
    show wreathFlip ≠ 1 by decide]

/-- The tenth-power source relation reduces exactly to an order-five factor check. -/
theorem y555WreathSpider_tenth (m : Y555Vertex → M) (hm : m none = 1) :
    y555WreathSpider m ^ 10 = 1 ↔
      (y555SpiderFirst m * y555SpiderSecond m) ^ 5 = 1 := by
  change y555WreathSpider m ^ (2 * 5) = 1 ↔ _
  rw [y555Wreath_outer_even_pow _ (y555WreathSpider_right m),
    y555WreathSpider_first m hm, y555WreathSpider_second m hm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
