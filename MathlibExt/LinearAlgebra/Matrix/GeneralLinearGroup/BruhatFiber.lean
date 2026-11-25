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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMonomialUniqueness
public import Mathlib.Data.Set.Prod

/-!
# Bruhat fibers for covers of the monomial special linear group

Given a group homomorphism `p : W →* MonomialSL F (Fin n)`, the Bruhat fiber
is the pullback of `bruhatMiddle` and `p`.  This file provides its upper
elementary actions, actions by a group mapping into `ker p`, distinguished
point and chosen lifts, and functorial maps of compatible projection data.

The construction is independent of any particular central extension.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix

universe u v w x y z u₁ u₂ u₃

namespace Matrix.GeneralLinearGroup

/-- The pullback of `bruhatMiddle` along a group homomorphism to the monomial
special linear group. -/
abbrev BruhatFiber (F : Type u) [Field F] (n : ℕ) {W : Type v} [Group W]
    (p : W →* MonomialSL F (Fin n)) : Type (max u v) :=
  Function.Pullback (bruhatMiddle (F := F) (ι := Fin n)) p

namespace BruhatFiber

variable {F : Type u} [Field F] {n : ℕ}
variable {W : Type v} [Group W] {p : W →* MonomialSL F (Fin n)}

/-- First projection of a Bruhat fiber. -/
abbrev fst (x : BruhatFiber F n p) : SpecialLinearGroup (Fin n) F :=
  x.val.1

/-- Second projection of a Bruhat fiber. -/
abbrev snd (x : BruhatFiber F n p) : W :=
  x.val.2

/-- The defining pullback square. -/
theorem prop_eq (x : BruhatFiber F n p) :
    bruhatMiddle (fst x) = p (snd x) :=
  x.2

@[ext]
theorem ext {x y : BruhatFiber F n p} (h1 : x.val.1 = y.val.1)
    (h2 : x.val.2 = y.val.2) : x = y := by
  apply Subtype.ext
  exact Prod.ext h1 h2

@[simp]
theorem mk_fst (s : SpecialLinearGroup (Fin n) F) (a : W)
    (h : bruhatMiddle s = p a) :
    fst (⟨(s, a), h⟩ : BruhatFiber F n p) = s :=
  rfl

@[simp]
theorem mk_snd (s : SpecialLinearGroup (Fin n) F) (a : W)
    (h : bruhatMiddle s = p a) :
    snd (⟨(s, a), h⟩ : BruhatFiber F n p) = a :=
  rfl

theorem coe_fst (x : BruhatFiber F n p) : (x.val : _).1 = fst x :=
  rfl

theorem coe_snd (x : BruhatFiber F n p) : (x.val : _).2 = snd x :=
  rfl

section BruhatMiddleInvariance

/-- Left multiplication by an upper-elementary element does not change the
Bruhat middle factor. -/
theorem bruhatMiddle_upper_left_mul
    (g : SpecialLinearGroup (Fin n) F)
    (a : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (UpperElementary.toSLHom a * g) = bruhatMiddle g := by
  let d := specialLinearBruhatDecomposition g
  have hSL : g =
      UpperElementary.toSLHom d.left *
        monomialSLHom F (Fin n) d.middle *
        UpperElementary.toSLHom d.right :=
    d.factorizationSL
  have hStep :
      UpperElementary.toSLHom a * g =
        UpperElementary.toSLHom a *
          (UpperElementary.toSLHom d.left *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom d.right) :=
    congrArg (UpperElementary.toSLHom a * ·) hSL
  have hMul : UpperElementary.toSLHom a * g =
      UpperElementary.toSLHom (a * d.left) *
        monomialSLHom F (Fin n) d.middle *
        UpperElementary.toSLHom d.right := by
    calc
      UpperElementary.toSLHom a * g =
          UpperElementary.toSLHom a *
            (UpperElementary.toSLHom d.left *
              monomialSLHom F (Fin n) d.middle *
              UpperElementary.toSLHom d.right) := hStep
      _ = (UpperElementary.toSLHom a * UpperElementary.toSLHom d.left) *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom d.right := by simp only [mul_assoc]
      _ = UpperElementary.toSLHom (a * d.left) *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom d.right := by rw [← map_mul]
  have hMid : bruhatMiddle (UpperElementary.toSLHom a * g) = d.middle :=
    bruhatMiddle_factorization_elim _ (a * d.left) d.middle d.right hMul
  have hOrig : bruhatMiddle g = d.middle := rfl
  rw [hMid, hOrig]

/-- Right multiplication by an upper-elementary element does not change the
Bruhat middle factor. -/
theorem bruhatMiddle_upper_right_mul
    (g : SpecialLinearGroup (Fin n) F)
    (a : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (g * UpperElementary.toSLHom a) = bruhatMiddle g := by
  let d := specialLinearBruhatDecomposition g
  have hSL : g =
      UpperElementary.toSLHom d.left *
        monomialSLHom F (Fin n) d.middle *
        UpperElementary.toSLHom d.right :=
    d.factorizationSL
  have hStep :
      g * UpperElementary.toSLHom a =
        (UpperElementary.toSLHom d.left *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom d.right) *
          UpperElementary.toSLHom a :=
    congrArg (· * UpperElementary.toSLHom a) hSL
  have hMul : g * UpperElementary.toSLHom a =
      UpperElementary.toSLHom d.left *
        monomialSLHom F (Fin n) d.middle *
        UpperElementary.toSLHom (d.right * a) := by
    calc
      g * UpperElementary.toSLHom a =
          (UpperElementary.toSLHom d.left *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom d.right) * UpperElementary.toSLHom a := hStep
      _ = UpperElementary.toSLHom d.left *
            monomialSLHom F (Fin n) d.middle *
            (UpperElementary.toSLHom d.right * UpperElementary.toSLHom a) := by
              simp only [mul_assoc]
      _ = UpperElementary.toSLHom d.left *
            monomialSLHom F (Fin n) d.middle *
            UpperElementary.toSLHom (d.right * a) := by rw [← map_mul]
  have hMid : bruhatMiddle (g * UpperElementary.toSLHom a) = d.middle :=
    bruhatMiddle_factorization_elim _ d.left d.middle (d.right * a) hMul
  have hOrig : bruhatMiddle g = d.middle := rfl
  rw [hMid, hOrig]

/-- Two-sided upper-elementary invariance. -/
theorem bruhatMiddle_upper_mul
    (g : SpecialLinearGroup (Fin n) F)
    (a b : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (UpperElementary.toSLHom a * g *
      UpperElementary.toSLHom b) = bruhatMiddle g := by
  rw [bruhatMiddle_upper_right_mul, bruhatMiddle_upper_left_mul]

theorem bruhatMiddle_one (F : Type u) [Field F] (n : ℕ) :
    bruhatMiddle (1 : SpecialLinearGroup (Fin n) F) = 1 := by
  have hSL : (1 : SpecialLinearGroup (Fin n) F) =
      UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin n) F) *
        monomialSLHom F (Fin n) (1 : MonomialSL F (Fin n)) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin n) F) := by
    simp
  exact bruhatMiddle_factorization_elim _ 1 1 1 hSL

end BruhatMiddleInvariance

section UpperActions

/-- Left upper-elementary action on a Bruhat fiber. -/
abbrev leftUpper (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : BruhatFiber F n p :=
  ⟨(UpperElementary.toSLHom a * x.val.1, x.val.2), by
    rw [bruhatMiddle_upper_left_mul]
    exact x.2⟩

/-- Right upper-elementary action on a Bruhat fiber. -/
abbrev rightUpper (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : BruhatFiber F n p :=
  ⟨(x.val.1 * UpperElementary.toSLHom a, x.val.2), by
    rw [bruhatMiddle_upper_right_mul]
    exact x.2⟩

theorem leftUpper_fst (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    fst (leftUpper a x) = UpperElementary.toSLHom a * fst x := rfl

theorem leftUpper_snd (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : snd (leftUpper a x) = snd x := rfl

theorem rightUpper_fst (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    fst (rightUpper a x) = fst x * UpperElementary.toSLHom a := rfl

theorem rightUpper_snd (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : snd (rightUpper a x) = snd x := rfl

theorem leftUpper_one (x : BruhatFiber F n p) :
    leftUpper (1 : upperElementarySubgroup (Fin n) F) x = x := by
  apply BruhatFiber.ext <;> simp

theorem rightUpper_one (x : BruhatFiber F n p) :
    rightUpper (1 : upperElementarySubgroup (Fin n) F) x = x := by
  apply BruhatFiber.ext <;> simp

theorem leftUpper_mul (a b : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    leftUpper (a * b) x = leftUpper a (leftUpper b x) := by
  apply BruhatFiber.ext <;> simp [mul_assoc, map_mul]

theorem rightUpper_mul (a b : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    rightUpper (a * b) x = rightUpper b (rightUpper a x) := by
  apply BruhatFiber.ext <;> simp [mul_assoc, map_mul]

theorem leftUpper_inv (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : leftUpper a⁻¹ (leftUpper a x) = x := by
  apply BruhatFiber.ext <;> simp [map_inv]

theorem rightUpper_inv (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : rightUpper a⁻¹ (rightUpper a x) = x := by
  apply BruhatFiber.ext <;> simp [map_inv, mul_assoc]

/-- Left upper action as a permutation. -/
abbrev leftUpperPerm (a : upperElementarySubgroup (Fin n) F) :
    Equiv.Perm (BruhatFiber F n p) where
  toFun := leftUpper a
  invFun := leftUpper a⁻¹
  left_inv := leftUpper_inv a
  right_inv x := by simpa using leftUpper_inv (p := p) a⁻¹ x

/-- Right upper action as a permutation. -/
abbrev rightUpperPerm (a : upperElementarySubgroup (Fin n) F) :
    Equiv.Perm (BruhatFiber F n p) where
  toFun := rightUpper a
  invFun := rightUpper a⁻¹
  left_inv := rightUpper_inv a
  right_inv x := by
    apply BruhatFiber.ext <;> simp [map_inv, mul_assoc]

theorem leftUpperPerm_apply (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : leftUpperPerm a x = leftUpper a x := rfl

theorem rightUpperPerm_apply (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : rightUpperPerm a x = rightUpper a x := rfl

theorem leftUpperPerm_one :
    leftUpperPerm (p := p) (1 : upperElementarySubgroup (Fin n) F) = 1 := by
  apply Equiv.ext
  intro x
  simp [leftUpperPerm, leftUpper_one]

theorem rightUpperPerm_one :
    rightUpperPerm (p := p) (1 : upperElementarySubgroup (Fin n) F) = 1 := by
  apply Equiv.ext
  intro x
  simp [rightUpperPerm, rightUpper_one]

theorem leftUpperPerm_mul (a b : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (p := p) (a * b) = leftUpperPerm a * leftUpperPerm b := by
  apply Equiv.ext
  intro x
  simp [leftUpperPerm, leftUpper_mul, Equiv.Perm.mul_apply]

theorem rightUpperPerm_mul (a b : upperElementarySubgroup (Fin n) F) :
    rightUpperPerm (p := p) (a * b) = rightUpperPerm b * rightUpperPerm a := by
  apply Equiv.ext
  intro x
  simp [rightUpperPerm, rightUpper_mul, Equiv.Perm.mul_apply]

theorem leftUpperPerm_inv (a : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (p := p) a⁻¹ = (leftUpperPerm a)⁻¹ := by
  apply Equiv.ext
  intro x
  simp [leftUpperPerm, Equiv.Perm.inv_def]

theorem rightUpperPerm_inv (a : upperElementarySubgroup (Fin n) F) :
    rightUpperPerm (p := p) a⁻¹ = (rightUpperPerm a)⁻¹ := by
  apply Equiv.ext
  intro x
  simp [rightUpperPerm, Equiv.Perm.inv_def]

/-- Homomorphism for the left upper action. -/
abbrev leftUpperHom : upperElementarySubgroup (Fin n) F →*
    Equiv.Perm (BruhatFiber F n p) where
  toFun := leftUpperPerm
  map_one' := leftUpperPerm_one
  map_mul' := leftUpperPerm_mul

/-- Homomorphism from the opposite upper group for the right action. -/
abbrev rightUpperHomOp : MulOpposite (upperElementarySubgroup (Fin n) F) →*
    Equiv.Perm (BruhatFiber F n p) where
  toFun a := rightUpperPerm a.unop
  map_one' := rightUpperPerm_one
  map_mul' a b := by
    change rightUpperPerm (b.unop * a.unop) =
      rightUpperPerm a.unop * rightUpperPerm b.unop
    rw [rightUpperPerm_mul]

theorem leftUpperHom_apply (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) : leftUpperHom (p := p) a x = leftUpper a x := rfl

theorem rightUpperHomOp_apply
    (a : MulOpposite (upperElementarySubgroup (Fin n) F))
    (x : BruhatFiber F n p) : rightUpperHomOp (p := p) a x = rightUpper a.unop x := rfl

theorem rightUpperHomOp_unop_apply (a : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    rightUpperHomOp (p := p) (MulOpposite.op a) x = rightUpper a x := rfl

theorem left_right_commute (a b : upperElementarySubgroup (Fin n) F)
    (x : BruhatFiber F n p) :
    leftUpper a (rightUpper b x) = rightUpper b (leftUpper a x) := by
  apply BruhatFiber.ext <;> simp [mul_assoc]

theorem leftUpperPerm_rightUpperPerm_comm
    (a b : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (p := p) a * rightUpperPerm b =
      rightUpperPerm b * leftUpperPerm a := by
  apply Equiv.ext
  intro x
  simp [leftUpperPerm, rightUpperPerm, left_right_commute, Equiv.Perm.mul_apply]

end UpperActions

section KernelAction

variable {C : Type w} [Group C] (ι : C →* W)
variable (hι : ∀ c, p (ι c) = 1)

/-- Action on the second coordinate by a homomorphism whose image is killed
by the fiber projection. -/
abbrev central (c : C) (x : BruhatFiber F n p) : BruhatFiber F n p :=
  ⟨(x.val.1, ι c * x.val.2), by
    calc
      bruhatMiddle x.val.1 = p x.val.2 := x.2
      _ = 1 * p x.val.2 := (one_mul _).symm
      _ = p (ι c) * p x.val.2 := by rw [hι c]
      _ = p (ι c * x.val.2) := (map_mul p _ _).symm⟩

theorem central_fst (c : C) (x : BruhatFiber F n p) :
    fst (central ι hι c x) = fst x := rfl

theorem central_snd (c : C) (x : BruhatFiber F n p) :
    snd (central ι hι c x) = ι c * snd x := rfl

theorem central_one (x : BruhatFiber F n p) : central ι hι 1 x = x := by
  apply BruhatFiber.ext <;> simp

theorem central_mul (c d : C) (x : BruhatFiber F n p) :
    central ι hι (c * d) x = central ι hι c (central ι hι d x) := by
  apply BruhatFiber.ext <;> simp [mul_assoc]

theorem central_inv (c : C) (x : BruhatFiber F n p) :
    central ι hι c⁻¹ (central ι hι c x) = x := by
  apply BruhatFiber.ext <;> simp

/-- Kernel-coordinate action as a permutation. -/
abbrev centralPerm (c : C) : Equiv.Perm (BruhatFiber F n p) where
  toFun := central ι hι c
  invFun := central ι hι c⁻¹
  left_inv := central_inv ι hι c
  right_inv x := by simpa using central_inv ι hι c⁻¹ x

theorem centralPerm_apply (c : C) (x : BruhatFiber F n p) :
    centralPerm ι hι c x = central ι hι c x := rfl

theorem centralPerm_one : centralPerm ι hι (1 : C) = 1 := by
  apply Equiv.ext
  intro x
  simp [centralPerm, central_one]

theorem centralPerm_mul (c d : C) :
    centralPerm ι hι (c * d) = centralPerm ι hι c * centralPerm ι hι d := by
  apply Equiv.ext
  intro x
  simp [centralPerm, central_mul, Equiv.Perm.mul_apply]

theorem centralPerm_inv (c : C) :
    centralPerm ι hι c⁻¹ = (centralPerm ι hι c)⁻¹ := by
  apply Equiv.ext
  intro x
  simp [centralPerm, Equiv.Perm.inv_def]

/-- Homomorphism for the kernel-coordinate action. -/
abbrev centralHom : C →* Equiv.Perm (BruhatFiber F n p) where
  toFun := centralPerm ι hι
  map_one' := centralPerm_one ι hι
  map_mul' := centralPerm_mul ι hι

theorem centralHom_apply (c : C) (x : BruhatFiber F n p) :
    centralHom ι hι c x = central ι hι c x := rfl

/-- The distinguished point with both coordinates equal to one. -/
abbrev basepoint (F : Type u) [Field F] (n : ℕ) {W : Type v} [Group W]
    (p : W →* MonomialSL F (Fin n)) : BruhatFiber F n p :=
  ⟨(1, 1), by rw [bruhatMiddle_one, map_one]⟩

theorem basepoint_fst : fst (basepoint F n p) = 1 := rfl

theorem basepoint_snd : snd (basepoint F n p) = 1 := rfl

/-- The kernel-coordinate action is faithful when the coordinate homomorphism
is injective. -/
theorem centralHom_injective (hιinj : Function.Injective ι) :
    Function.Injective (centralHom ι hι) := by
  intro c d h
  have hAct := congrArg (fun e : Equiv.Perm (BruhatFiber F n p) =>
    e (basepoint F n p)) h
  have hSnd := congrArg (fun q => snd q) hAct
  apply hιinj
  simpa [centralHom_apply, central_snd, basepoint_snd] using hSnd

theorem central_left_commute (c : C)
    (a : upperElementarySubgroup (Fin n) F) (x : BruhatFiber F n p) :
    central ι hι c (leftUpper a x) = leftUpper a (central ι hι c x) := by
  apply BruhatFiber.ext <;> simp

theorem central_right_commute (c : C)
    (a : upperElementarySubgroup (Fin n) F) (x : BruhatFiber F n p) :
    central ι hι c (rightUpper a x) = rightUpper a (central ι hι c x) := by
  apply BruhatFiber.ext <;> simp

theorem centralPerm_leftUpperPerm_comm (c : C)
    (a : upperElementarySubgroup (Fin n) F) :
    centralPerm ι hι c * leftUpperPerm (p := p) a =
      leftUpperPerm a * centralPerm ι hι c := by
  apply Equiv.ext
  intro q
  simp [centralPerm, leftUpperPerm, central_left_commute, Equiv.Perm.mul_apply]

theorem centralPerm_rightUpperPerm_comm (c : C)
    (a : upperElementarySubgroup (Fin n) F) :
    centralPerm ι hι c * rightUpperPerm (p := p) a =
      rightUpperPerm a * centralPerm ι hι c := by
  apply Equiv.ext
  intro q
  simp [centralPerm, rightUpperPerm, central_right_commute, Equiv.Perm.mul_apply]

end KernelAction

section Maps

/-- Compatible homomorphisms between two sets of Bruhat projection data. -/
structure MapData (F : Type u) [Field F] (K : Type v) [Field K] (n : ℕ)
    {W : Type w} [Group W] {W' : Type x} [Group W']
    (p : W →* MonomialSL F (Fin n))
    (q : W' →* MonomialSL K (Fin n)) where
  mapSL : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) K
  mapMiddle : MonomialSL F (Fin n) →* MonomialSL K (Fin n)
  mapFiber : W →* W'
  commSL : ∀ s, bruhatMiddle (mapSL s) = mapMiddle (bruhatMiddle s)
  commFiber : ∀ a, q (mapFiber a) = mapMiddle (p a)

namespace MapData

/-- Identity compatible projection data. -/
def id (F : Type u) [Field F] (n : ℕ) {W : Type w} [Group W]
    (p : W →* MonomialSL F (Fin n)) : MapData F F n p p where
  mapSL := MonoidHom.id _
  mapMiddle := MonoidHom.id _
  mapFiber := MonoidHom.id _
  commSL _ := rfl
  commFiber _ := rfl

/-- Composition of compatible projection data. -/
def comp {K : Type v} [Field K] {L : Type x} [Field L] {n : ℕ}
    {W₁ : Type w} [Group W₁] {W₂ : Type y} [Group W₂]
    {W₃ : Type z} [Group W₃]
    {p₁ : W₁ →* MonomialSL F (Fin n)}
    {p₂ : W₂ →* MonomialSL K (Fin n)}
    {p₃ : W₃ →* MonomialSL L (Fin n)}
    (ψ : MapData K L n p₂ p₃) (φ : MapData F K n p₁ p₂) :
    MapData F L n p₁ p₃ where
  mapSL := ψ.mapSL.comp φ.mapSL
  mapMiddle := ψ.mapMiddle.comp φ.mapMiddle
  mapFiber := ψ.mapFiber.comp φ.mapFiber
  commSL s := by
    rw [MonoidHom.comp_apply, ψ.commSL, MonoidHom.comp_apply, φ.commSL]
  commFiber a := by
    rw [MonoidHom.comp_apply, ψ.commFiber, MonoidHom.comp_apply, φ.commFiber]

end MapData

/-- Map between Bruhat fibers induced by compatible projection data. -/
def map {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)}
    (φ : MapData F K n p q) (a : BruhatFiber F n p) : BruhatFiber K n q :=
  Function.mapPullback
    (f₁ := bruhatMiddle (F := F) (ι := Fin n)) (g₁ := p)
    (f₂ := bruhatMiddle (F := K) (ι := Fin n)) (g₂ := q)
    φ.mapSL φ.mapMiddle φ.mapFiber
    (funext φ.commSL) (funext φ.commFiber) a

theorem map_fst {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    (a : BruhatFiber F n p) : fst (map φ a) = φ.mapSL (fst a) := rfl

theorem map_snd {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    (a : BruhatFiber F n p) : snd (map φ a) = φ.mapFiber (snd a) := rfl

theorem map_wellDefined {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    (a : BruhatFiber F n p) :
    bruhatMiddle (φ.mapSL a.val.1) = q (φ.mapFiber a.val.2) :=
  (map φ a).2

@[simp] theorem map_id (a : BruhatFiber F n p) :
    map (MapData.id F n p) a = a := by
  apply BruhatFiber.ext <;> rfl

theorem map_comp {K : Type u₁} [Field K] {L : Type u₂} [Field L]
    {W₂ : Type u₃} [Group W₂] {W₃ : Type z} [Group W₃]
    {p₂ : W₂ →* MonomialSL K (Fin n)}
    {p₃ : W₃ →* MonomialSL L (Fin n)}
    (φ : MapData F K n p p₂) (ψ : MapData K L n p₂ p₃)
    (a : BruhatFiber F n p) :
    map (MapData.comp ψ φ) a = map ψ (map φ a) := by
  apply BruhatFiber.ext <;> rfl

/-- Naturality of the left upper action under compatible projection data. -/
theorem map_leftUpper {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    (a : upperElementarySubgroup (Fin n) F)
    (b : upperElementarySubgroup (Fin n) K)
    (h : φ.mapSL (UpperElementary.toSLHom a) = UpperElementary.toSLHom b)
    (x : BruhatFiber F n p) :
    map φ (leftUpper a x) = leftUpper b (map φ x) := by
  apply BruhatFiber.ext
  · change φ.mapSL (UpperElementary.toSLHom a * x.val.1) =
      UpperElementary.toSLHom b * φ.mapSL x.val.1
    rw [map_mul, h]
  · rfl

/-- Naturality of the right upper action under compatible projection data. -/
theorem map_rightUpper {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    (a : upperElementarySubgroup (Fin n) F)
    (b : upperElementarySubgroup (Fin n) K)
    (h : φ.mapSL (UpperElementary.toSLHom a) = UpperElementary.toSLHom b)
    (x : BruhatFiber F n p) :
    map φ (rightUpper a x) = rightUpper b (map φ x) := by
  apply BruhatFiber.ext
  · change φ.mapSL (x.val.1 * UpperElementary.toSLHom a) =
      φ.mapSL x.val.1 * UpperElementary.toSLHom b
    rw [map_mul, h]
  · rfl

/-- Naturality of a kernel-coordinate action under compatible projection
data. -/
theorem map_central {K : Type u₁} [Field K] {W' : Type u₂} [Group W']
    {q : W' →* MonomialSL K (Fin n)} (φ : MapData F K n p q)
    {C : Type x} [Group C] {C' : Type y} [Group C']
    (ι : C →* W) (hι : ∀ c, p (ι c) = 1)
    (ι' : C' →* W') (hι' : ∀ c, q (ι' c) = 1)
    (mapC : C →* C') (hC : ∀ c, φ.mapFiber (ι c) = ι' (mapC c))
    (c : C) (a : BruhatFiber F n p) :
    map φ (central ι hι c a) = central ι' hι' (mapC c) (map φ a) := by
  apply BruhatFiber.ext
  · rfl
  · change φ.mapFiber (ι c * a.val.2) = ι' (mapC c) * φ.mapFiber a.val.2
    rw [map_mul, hC]

end Maps

section ChosenLift

/-- A chosen lift through a surjective fiber projection. -/
noncomputable def chooseLift (hp : Function.Surjective p)
    (m : MonomialSL F (Fin n)) : W :=
  Classical.choose (hp m)

theorem chooseLift_spec (hp : Function.Surjective p)
    (m : MonomialSL F (Fin n)) : p (chooseLift hp m) = m :=
  Classical.choose_spec (hp m)

/-- A chosen point of the Bruhat fiber above a special linear matrix. -/
noncomputable def mk (hp : Function.Surjective p)
    (s : SpecialLinearGroup (Fin n) F) : BruhatFiber F n p :=
  ⟨(s, chooseLift hp (bruhatMiddle s)), by rw [chooseLift_spec]⟩

theorem mk_point_fst (hp : Function.Surjective p)
    (s : SpecialLinearGroup (Fin n) F) : fst (mk hp s) = s := rfl

theorem mk_point_snd_proj (hp : Function.Surjective p)
    (s : SpecialLinearGroup (Fin n) F) :
    p (snd (mk hp s)) = bruhatMiddle s :=
  chooseLift_spec hp (bruhatMiddle s)

theorem mk_point_prop (hp : Function.Surjective p)
    (s : SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (fst (mk hp s)) = p (snd (mk hp s)) :=
  (mk hp s).2

end ChosenLift

end BruhatFiber

end Matrix.GeneralLinearGroup
