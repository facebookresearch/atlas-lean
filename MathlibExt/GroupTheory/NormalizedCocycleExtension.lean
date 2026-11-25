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

public import MathlibExt.GroupTheory.CentralExtension
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Normalized central 2-cocycle extensions

Central extension constructed from a normalized multiplicative 2-cocycle
with trivial action.
-/

@[expose] public section

universe u v w t u3 v3

namespace NormalizedCocycleExtension

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]

/-- A normalized central (multiplicative) 2-cocycle `c : G → G → A`
with trivial action.

Fields:
- `cocycle g h` is the value `c g h`;
- `one_left : c 1 g = 1`;
- `one_right : c g 1 = 1`;
- `cocycle_assoc : c g h * c (g*h) k = c g (h*k) * c h k`. -/
structure NormalizedCocycle (G : Type u) (A : Type v)
    [Group G] [CommGroup A] where
  cocycle : G → G → A
  one_left : ∀ g : G, cocycle 1 g = 1
  one_right : ∀ g : G, cocycle g 1 = 1
  cocycle_assoc :
    ∀ g h k : G, cocycle g h * cocycle (g * h) k =
      cocycle g (h * k) * cocycle h k

instance : CoeFun (NormalizedCocycle G A) (fun _ => G → G → A) where
  coe c := c.cocycle

@[simp]
theorem cocycle_one_left (c : NormalizedCocycle G A) (g : G) :
    c.cocycle 1 g = 1 :=
  c.one_left g

@[simp]
theorem cocycle_one_right (c : NormalizedCocycle G A) (g : G) :
    c.cocycle g 1 = 1 :=
  c.one_right g

@[simp]
theorem coe_one_left (c : NormalizedCocycle G A) (g : G) :
    (c : G → G → A) 1 g = 1 :=
  c.one_left g

@[simp]
theorem coe_one_right (c : NormalizedCocycle G A) (g : G) :
    (c : G → G → A) g 1 = 1 :=
  c.one_right g

theorem cocycle_assoc' (c : NormalizedCocycle G A) (g h k : G) :
    c.cocycle g h * c.cocycle (g * h) k =
      c.cocycle g (h * k) * c.cocycle h k :=
  c.cocycle_assoc g h k

theorem cocycle_assoc_coe (c : NormalizedCocycle G A) (g h k : G) :
    (c : G → G → A) g h * (c : G → G → A) (g * h) k =
      (c : G → G → A) g (h * k) * (c : G → G → A) h k :=
  c.cocycle_assoc g h k

@[simp]
theorem cocycle_one_one (c : NormalizedCocycle G A) :
    c.cocycle 1 1 = (1 : A) :=
  c.one_left 1

theorem cocycle_inv_eq {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (c : NormalizedCocycle G A) (g : G) :
    c.cocycle g g⁻¹ = c.cocycle g⁻¹ g := by
  simpa [mul_inv_cancel, inv_mul_cancel, c.one_left, c.one_right]
    using c.cocycle_assoc g g⁻¹ g

section Extension

structure Extension {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (c : NormalizedCocycle G A) where
  base : G
  coeff : A
  deriving DecidableEq

@[ext]
theorem Extension.ext {G : Type u} {A : Type v} [Group G] [CommGroup A]
    {c : NormalizedCocycle G A} {x y : Extension c}
    (hbase : x.base = y.base) (hcoeff : x.coeff = y.coeff) : x = y := by
  cases x; cases y; simp_all

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]
  (c : NormalizedCocycle G A)

instance : Mul (Extension c) where
  mul x y := ⟨x.base * y.base, x.coeff * y.coeff * c.cocycle x.base y.base⟩

instance : One (Extension c) where
  one := ⟨1, 1⟩

instance : Inv (Extension c) where
  inv x := ⟨x.base⁻¹, x.coeff⁻¹ * (c.cocycle x.base⁻¹ x.base)⁻¹⟩

@[simp]
theorem one_base : (1 : Extension c).base = (1 : G) := rfl

@[simp]
theorem one_coeff : (1 : Extension c).coeff = (1 : A) := rfl

@[simp]
theorem mul_base (x y : Extension c) :
    (x * y).base = x.base * y.base := rfl

@[simp]
theorem mul_coeff (x y : Extension c) :
    (x * y).coeff = x.coeff * y.coeff * c.cocycle x.base y.base := rfl

@[simp]
theorem inv_base (x : Extension c) :
    (x⁻¹ : Extension c).base = x.base⁻¹ := rfl

theorem inv_coeff (x : Extension c) :
    (x⁻¹ : Extension c).coeff =
      x.coeff⁻¹ * (c.cocycle x.base⁻¹ x.base)⁻¹ := rfl

theorem inv_coeff' (x : Extension c) :
    (x⁻¹ : Extension c).coeff =
      x.coeff⁻¹ * (c.cocycle x.base x.base⁻¹)⁻¹ := by
  rw [inv_coeff, cocycle_inv_eq c x.base]

instance : Group (Extension c) where
  mul_assoc x y z := by
    apply Extension.ext
    · simp [mul_assoc]
    · simp only [mul_coeff, mul_base]
      have h := c.cocycle_assoc x.base y.base z.base
      calc x.coeff * y.coeff * c.cocycle x.base y.base * z.coeff *
            c.cocycle (x.base * y.base) z.base
          = x.coeff * y.coeff * z.coeff *
              (c.cocycle x.base y.base * c.cocycle (x.base * y.base) z.base) := by
            ac_rfl
        _ = x.coeff * y.coeff * z.coeff *
              (c.cocycle x.base (y.base * z.base) * c.cocycle y.base z.base) := by
            rw [h]
        _ = x.coeff * (y.coeff * z.coeff * c.cocycle y.base z.base) *
              c.cocycle x.base (y.base * z.base) := by
            ac_rfl
  one_mul x := by
    apply Extension.ext
    · simp
    · simp only [mul_coeff, one_base, one_coeff, c.one_left]
      simp [mul_one]
  mul_one x := by
    apply Extension.ext
    · simp
    · simp only [mul_coeff, one_base, one_coeff, c.one_right]
      simp [mul_one]
  inv_mul_cancel x := by
    apply Extension.ext
    · simp
    · simp only [mul_coeff, inv_coeff, inv_base]
      calc x.coeff⁻¹ * (c.cocycle x.base⁻¹ x.base)⁻¹ * x.coeff *
            c.cocycle x.base⁻¹ x.base
          = x.coeff⁻¹ * x.coeff *
              ((c.cocycle x.base⁻¹ x.base)⁻¹ * c.cocycle x.base⁻¹ x.base) := by
            ac_rfl
        _ = 1 * ((c.cocycle x.base⁻¹ x.base)⁻¹ * c.cocycle x.base⁻¹ x.base) := by
            rw [inv_mul_cancel]
        _ = 1 := by
            rw [one_mul, inv_mul_cancel]

def projHom : Extension c →* G where
  toFun x := x.base
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem projHom_apply (x : Extension c) : projHom c x = x.base := rfl

@[simp]
theorem projHom_one : projHom c (1 : Extension c) = 1 := rfl

@[simp]
theorem projHom_mul (x y : Extension c) :
    projHom c (x * y) = projHom c x * projHom c y := rfl

def inlHom : A →* Extension c where
  toFun a := ⟨1, a⟩
  map_one' := rfl
  map_mul' a b := by
    apply Extension.ext
    · simp
    · simp only [mul_coeff]
      have h : c.cocycle 1 1 = (1 : A) := c.one_left 1
      simp [h, mul_one]

@[simp]
theorem inlHom_base (a : A) : (inlHom c a).base = 1 := rfl

@[simp]
theorem inlHom_coeff (a : A) : (inlHom c a).coeff = a := rfl

def extension : GroupExtension A (Extension c) G where
  inl := inlHom c
  rightHom := projHom c
  inl_injective := by
    intro a b h
    have hcoeff : (inlHom c a).coeff = (inlHom c b).coeff :=
      congrArg Extension.coeff h
    simpa using hcoeff
  range_inl_eq_ker_rightHom := by
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, projHom]
    constructor
    · rintro ⟨a, rfl⟩
      rfl
    · intro hx
      change x.base = 1 at hx
      exact ⟨x.coeff, by
        apply Extension.ext
        · simpa using hx.symm
        · rfl⟩
  rightHom_surjective := by
    intro g
    exact ⟨⟨g, 1⟩, rfl⟩

@[simp]
theorem extension_inl (a : A) : (extension c).inl a = inlHom c a := rfl

@[simp]
theorem extension_rightHom (x : Extension c) :
    (extension c).rightHom x = projHom c x := rfl

theorem isCentral : (extension c).IsCentral := by
  intro x hx
  rw [MonoidHom.mem_ker, extension_rightHom] at hx
  change x.base = 1 at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Extension.ext
  · simp [hx, mul_one, one_mul]
  · simp only [mul_coeff, hx]
    have h1 : c.cocycle y.base 1 = (1 : A) := c.one_right y.base
    have h2 : c.cocycle 1 y.base = (1 : A) := c.one_left y.base
    calc y.coeff * x.coeff * c.cocycle y.base 1
        = y.coeff * x.coeff := by rw [h1, mul_one]
      _ = x.coeff * y.coeff := by rw [mul_comm]
      _ = x.coeff * y.coeff * c.cocycle 1 y.base := by rw [h2, mul_one]

end Extension

end NormalizedCocycleExtension

section Functoriality

namespace NormalizedCocycleExtension

/-- Compatible map between normalized cocycles.

Data:
- `f : G →* G'` (base hom);
- `g : A →* A'` (coefficient hom);
- `q : G → A'` with `q 1 = 1`;
- `compat : g (c x y) * q (x*y) = q x * q y * d (f x) (f y)`.

Induced map is `(x,a) ↦ (f x, g a * q x)`. -/
structure CompatibleMap {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    (c : NormalizedCocycle G₁ A₁) (d : NormalizedCocycle G₂ A₂) where
  f : G₁ →* G₂
  g : A₁ →* A₂
  q : G₁ → A₂
  q_one : q 1 = 1
  compat :
    ∀ x y : G₁, g (c.cocycle x y) * q (x * y) =
      q x * q y * d.cocycle (f x) (f y)

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]
variable {G' : Type w} {A' : Type t} [Group G'] [CommGroup A']
variable {c : NormalizedCocycle G A} {d : NormalizedCocycle G' A'}

def CompatibleMap.baseHom {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) : G →* G' :=
  h.f

def CompatibleMap.coeffHom {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) : A →* A' :=
  h.g

def CompatibleMap.correction {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) : G → A' :=
  h.q

@[simp]
theorem CompatibleMap.q_one' {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) :
    h.q 1 = 1 :=
  h.q_one

theorem CompatibleMap.compat' {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) (x y : G) :
    h.g (c.cocycle x y) * h.q (x * y) =
      h.q x * h.q y * d.cocycle (h.f x) (h.f y) :=
  h.compat x y

theorem CompatibleMap.compat_coe {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) (x y : G) :
    h.g ((c : G → G → A) x y) * h.q (x * y) =
      h.q x * h.q y * (d : G' → G' → A') (h.f x) (h.f y) :=
  h.compat x y

def CompatibleMap.toHom {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) :
    Extension c →* Extension d where
  toFun x := ⟨h.f x.base, h.g x.coeff * h.q x.base⟩
  map_one' := by
    apply Extension.ext
    · simp [h.f.map_one]
    · simp [h.g.map_one, h.q_one]
  map_mul' x y := by
    apply Extension.ext
    · simp [map_mul]
    · calc h.g (x.coeff * y.coeff * c.cocycle x.base y.base) * h.q (x.base * y.base)
          = h.g x.coeff * h.g y.coeff * h.g (c.cocycle x.base y.base) *
              h.q (x.base * y.base) := by
            simp [map_mul]
        _ = h.g x.coeff * h.g y.coeff *
              (h.g (c.cocycle x.base y.base) * h.q (x.base * y.base)) := by
            simp [mul_assoc]
        _ = h.g x.coeff * h.g y.coeff *
              (h.q x.base * h.q y.base * d.cocycle (h.f x.base) (h.f y.base)) := by
            rw [h.compat x.base y.base]
        _ = (h.g x.coeff * h.q x.base) * (h.g y.coeff * h.q y.base) *
              d.cocycle (h.f x.base) (h.f y.base) := by
            simp [mul_assoc, mul_comm, mul_left_comm]

@[simp]
theorem CompatibleMap.toHom_base {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d)
    (x : Extension c) : (h.toHom x).base = h.f x.base := rfl

@[simp]
theorem CompatibleMap.toHom_coeff {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d)
    (x : Extension c) :
    (h.toHom x).coeff = h.g x.coeff * h.q x.base := rfl

theorem CompatibleMap.toHom_inl {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) (a : A) :
    h.toHom (inlHom c a) = inlHom d (h.g a) := by
  apply Extension.ext
  · simp [h.f.map_one]
  · simp [h.q_one]

@[simp]
theorem CompatibleMap.toHom_inl_coeff {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) (a : A) :
    (h.toHom (inlHom c a)).coeff = h.g a := by
  simp [CompatibleMap.toHom_inl]

theorem CompatibleMap.toHom_proj {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d)
    (x : Extension c) :
    projHom d (h.toHom x) = h.f (projHom c x) := rfl

theorem CompatibleMap.comp_proj {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) :
    (projHom d).comp h.toHom = h.f.comp (projHom c) := by
  ext x; rfl

theorem CompatibleMap.inl_comp {c : NormalizedCocycle G A}
    {d : NormalizedCocycle G' A'} (h : CompatibleMap c d) :
    h.toHom.comp (inlHom c) = (inlHom d).comp h.g := by
  apply MonoidHom.ext
  intro a
  exact CompatibleMap.toHom_inl h a

def CompatibleMap.id {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (c : NormalizedCocycle G A) : CompatibleMap c c where
  f := MonoidHom.id G
  g := MonoidHom.id A
  q := fun _ => 1
  q_one := rfl
  compat x y := by
    simp only [MonoidHom.id_apply, mul_one, one_mul]

theorem CompatibleMap.id_f (c : NormalizedCocycle G A) :
    (CompatibleMap.id c).f = MonoidHom.id G := by
  rfl

theorem CompatibleMap.id_g (c : NormalizedCocycle G A) :
    (CompatibleMap.id c).g = MonoidHom.id A := by
  rfl

theorem CompatibleMap.id_q (c : NormalizedCocycle G A) (x : G) :
    (CompatibleMap.id c).q x = 1 := by
  rfl

def CompatibleMap.comp {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃) :
    CompatibleMap c₁ c₃ where
  f := h₂.f.comp h₁.f
  g := h₂.g.comp h₁.g
  q x := h₂.g (h₁.q x) * h₂.q (h₁.f x)
  q_one := by
    simp [h₁.q_one, h₂.q_one, map_one, h₁.f.map_one]
  compat x y := by
    simp only [MonoidHom.comp_apply]
    have h1c := h₁.compat x y
    have h2c := h₂.compat (h₁.f x) (h₁.f y)
    calc h₂.g (h₁.g (c₁.cocycle x y)) *
          (h₂.g (h₁.q (x * y)) * h₂.q (h₁.f (x * y)))
        = h₂.g (h₁.g (c₁.cocycle x y) * h₁.q (x * y)) *
            h₂.q (h₁.f (x * y)) := by
          calc h₂.g (h₁.g (c₁.cocycle x y)) * (h₂.g (h₁.q (x * y)) * h₂.q (h₁.f (x * y)))
              = h₂.g (h₁.g (c₁.cocycle x y)) * h₂.g (h₁.q (x * y)) * h₂.q (h₁.f (x * y)) := by
                rw [mul_assoc]
            _ = h₂.g (h₁.g (c₁.cocycle x y) * h₁.q (x * y)) * h₂.q (h₁.f (x * y)) := by
                rw [← (h₂.g : A₂ →* A₃).map_mul]
      _ = h₂.g (h₁.q x * h₁.q y * c₂.cocycle (h₁.f x) (h₁.f y)) *
            h₂.q (h₁.f (x * y)) := by
          rw [h1c]
      _ = h₂.g (h₁.q x) * h₂.g (h₁.q y) * h₂.g (c₂.cocycle (h₁.f x) (h₁.f y)) *
            h₂.q (h₁.f (x * y)) := by
          simp [map_mul]
      _ = h₂.g (h₁.q x) * h₂.g (h₁.q y) *
            (h₂.g (c₂.cocycle (h₁.f x) (h₁.f y)) * h₂.q (h₁.f (x * y))) := by
          ac_rfl
      _ = h₂.g (h₁.q x) * h₂.g (h₁.q y) *
            (h₂.g (c₂.cocycle (h₁.f x) (h₁.f y)) *
              h₂.q (h₁.f x * h₁.f y)) := by
          rw [map_mul (h₁.f)]
      _ = h₂.g (h₁.q x) * h₂.g (h₁.q y) *
            (h₂.q (h₁.f x) * h₂.q (h₁.f y) *
              c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y))) := by
          rw [h2c]
      _ = (h₂.g (h₁.q x) * h₂.q (h₁.f x)) *
            (h₂.g (h₁.q y) * h₂.q (h₁.f y)) *
            c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y)) := by
          calc h₂.g (h₁.q x) * h₂.g (h₁.q y) *
                (h₂.q (h₁.f x) * h₂.q (h₁.f y) *
                  c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y)))
              = h₂.g (h₁.q x) * h₂.q (h₁.f x) *
                (h₂.g (h₁.q y) * h₂.q (h₁.f y) *
                  c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y))) := by
                rw [show h₂.g (h₁.q x) * h₂.g (h₁.q y) *
                    (h₂.q (h₁.f x) * h₂.q (h₁.f y) *
                      c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y))) =
                    h₂.g (h₁.q x) * h₂.q (h₁.f x) *
                    (h₂.g (h₁.q y) * h₂.q (h₁.f y) *
                      c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y))) from by
                  ac_rfl]
            _ = (h₂.g (h₁.q x) * h₂.q (h₁.f x)) *
                (h₂.g (h₁.q y) * h₂.q (h₁.f y)) *
                c₃.cocycle (h₂.f (h₁.f x)) (h₂.f (h₁.f y)) := by
                simp only [mul_assoc]

theorem CompatibleMap.comp_f {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃) :
    (h₁.comp h₂).f = h₂.f.comp h₁.f :=
  rfl

theorem CompatibleMap.comp_g {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃) :
    (h₁.comp h₂).g = h₂.g.comp h₁.g :=
  rfl

theorem CompatibleMap.comp_q {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃) (x : G₁) :
    (h₁.comp h₂).q x = h₂.g (h₁.q x) * h₂.q (h₁.f x) :=
  rfl

theorem CompatibleMap.toHom_id (c : NormalizedCocycle G A) :
    (CompatibleMap.id c).toHom = MonoidHom.id (Extension c) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · rfl
  · change (MonoidHom.id A) x.coeff * (1 : A) = x.coeff
    simp

@[simp]
theorem CompatibleMap.toHom_id_apply (c : NormalizedCocycle G A)
    (x : Extension c) : (CompatibleMap.id c).toHom x = x := by
  have h := CompatibleMap.toHom_id c
  have hx : (CompatibleMap.id c).toHom x = MonoidHom.id (Extension c) x := by
    rw [h]
  simpa using hx

theorem CompatibleMap.toHom_comp {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃) :
    (h₁.comp h₂).toHom = (h₂.toHom).comp (h₁.toHom) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · simp [CompatibleMap.comp, MonoidHom.comp_apply]
  · simp only [CompatibleMap.toHom_coeff, CompatibleMap.comp_q,
        CompatibleMap.comp_g, MonoidHom.comp_apply, map_mul]
    ac_rfl

@[simp]
theorem CompatibleMap.toHom_comp_apply {G₁ : Type u} {A₁ : Type v} [Group G₁] [CommGroup A₁]
    {G₂ : Type w} {A₂ : Type t} [Group G₂] [CommGroup A₂]
    {G₃ : Type u3} {A₃ : Type v3} [Group G₃] [CommGroup A₃]
    {c₁ : NormalizedCocycle G₁ A₁} {c₂ : NormalizedCocycle G₂ A₂}
    {c₃ : NormalizedCocycle G₃ A₃}
    (h₁ : CompatibleMap c₁ c₂) (h₂ : CompatibleMap c₂ c₃)
    (x : Extension c₁) :
    (h₁.comp h₂).toHom x = h₂.toHom (h₁.toHom x) := by
  have h := CompatibleMap.toHom_comp h₁ h₂
  have hx : (h₁.comp h₂).toHom x = (h₂.toHom.comp h₁.toHom) x := by
    rw [h]
  exact hx

end NormalizedCocycleExtension

end Functoriality

end
