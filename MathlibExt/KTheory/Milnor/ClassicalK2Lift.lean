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

public import MathlibExt.KTheory.Milnor.ClassicalDegreeLift
public import MathlibExt.KTheory.Milnor.ClassicalK2Extensionality

/-!
# Universal lift from bilinear Steinberg symbols to Milnor `K₂`

For a field `F`, any `ℤ`-bilinear map
`β : (Additive Fˣ) × (Additive Fˣ) → A` vanishing on Steinberg pairs
`{a, 1-a}` induces a `ℤ`-linear map `MilnorK F 2 →ₗ[ℤ] A` on symbols.

`MilnorK F 2` is canonically `MilnorKRing.degree F 2`, the degree-`2`
homogeneous component of the Milnor `K`-ring. The textbook quotient
`MilnorKPresentation F 2 = TensorRing.degree F 2 ⧸ steinbergDegreeSpanInDegree F 2`
presents it via `classicalPresentationEquiv F 2`. The construction lifts `β`
through `PiTensorProduct.lift` to the second tensor power, composes with the
general `TensorAlgebra.degreeToTensorPower` identification of
`↥(TensorRing.degree F 2)` with `TensorPower ℤ 2 (Additive Fˣ)`.  The generic
arbitrary-degree API performs the span induction and quotient descent; this
file only identifies the degree-two Steinberg hypothesis with the generic
adjacent condition.  The retained structural wrapper
`IsSteinberg.le_ker_degreeK2Lift` is a short `calc` using the presentation
equality.

This file also provides a reusable bundled API `SteinbergBimap` for
separately multiplicative Steinberg symbols. A `SteinbergBimap F A` is a
function `Fˣ → Fˣ → A` multiplicative-to-additive in each argument and
vanishing on every Steinberg pair `a, 1-a`. It is `CoeFun`-callable,
converts to the `Fin 2` `MultilinearMap` expected by the core lift, and
exposes a universal lift `liftK2OfBimap` to `MilnorK F 2 →ₗ[ℤ] A`. The
conversion encapsulates the linearity boilerplate previously repeated in
`Ring/K2/MilnorComparison.lean`.

## Main definitions

* `tensorPairDegree F a b` – canonical degree-two representative `ι a * ι b`.
* `IsSteinberg F β` – `β` vanishes on every `(a, 1-a)` Steinberg pair.
* `degreeK2Lift F β` – `ℤ`-linear map on `↥(degree F 2)` via tensor-power lift.
* `liftK2 F β hβ` – degree-two facade over the arbitrary-degree adjacent
  Steinberg lift.
* `MilnorK.SteinbergBimap F A` – bundled separately multiplicative
  Steinberg symbol `Fˣ → Fˣ → A`.
* `SteinbergBimap.toMultilinearMap` – conversion to
  `MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A`.
* `SteinbergBimap.compLinearMap` – postcomposition with `A →ₗ[ℤ] B`.
* `MilnorK.liftK2OfBimap` – universal lift from a `SteinbergBimap` to
  `MilnorK F 2 →ₗ[ℤ] A` via `liftK2`.

## Main results

* `degreeK2Lift_tensorPairDegree` – `degreeK2Lift` evaluates `β` on
  `tensorPairDegree`.
* `IsSteinberg.le_ker_steinbergDegreeSpanInDegree` – compatibility kernel lemma
  obtained from the generic arbitrary-degree span theorem.
* `IsSteinberg.le_ker_degreeK2Lift` – short structural wrapper via the
  presentation equality `steinbergDegreeSubmodule = steinbergDegreeSpanInDegree`.
* `liftK2_mk`, `liftK2_tensorPairDegree`, `liftK2_k2Symbol` – computations of
  `liftK2` on `mk`, the canonical pair, and `k2Symbol`.
* `k2Symbol_eq_mk_tensorPairDegree` – identity `k2Symbol F a b = mk 2 (⊗ a b)`,
  proved directly in `MilnorKRing.degree F 2`.
* `liftK2_ext` – two lifts agreeing on pure symbol pairs are equal.
* `SteinbergBimap.map_one_left`, `map_one_right`, `map_inv_left`,
  `map_inv_right`, `map_zpow_left`, `map_zpow_right` – elementary consequences
  of separate multiplicativity.
* `SteinbergBimap.toMultilinearMap_apply` – `toMultilinearMap` evaluates the
  bundled function.
* `SteinbergBimap.isSteinberg_toMultilinearMap` – the conversion satisfies
  `IsSteinberg`.
* `liftK2OfBimap_k2Symbol` – `liftK2OfBimap` evaluates the bimap on symbols.
* `SteinbergBimap.ext` – extensionality for `SteinbergBimap`.
* `SteinbergBimap.compLinearMap_apply` and `liftK2OfBimap_comp` – functoriality
  for postcomposition.
-/

@[expose] public section

open TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]

/-- Canonical degree-two element `ι (ofMul a) * ι (ofMul b)` viewed in
`↥(TensorRing.degree F 2)`. -/
def tensorPairDegree (a b : Fˣ) : ↥(TensorRing.degree F 2) :=
  ⟨TensorAlgebra.ι ℤ (Additive.ofMul a) *
      TensorAlgebra.ι ℤ (Additive.ofMul b),
    ι_mul_ι_mem_degree_two F a b⟩

/-- The underlying tensor-ring element of `tensorPairDegree` is `ι a * ι b`. -/
@[simp]
theorem tensorPairDegree_coe (a b : Fˣ) :
    (tensorPairDegree F a b : TensorRing F) =
      TensorAlgebra.ι ℤ (Additive.ofMul a) *
        TensorAlgebra.ι ℤ (Additive.ofMul b) :=
  rfl

/-- Let `F` be a field, `A` an additive commutative group with a `ℤ`-module
structure, and `β` a `ℤ`-bilinear map from two copies of `Additive Fˣ` to `A`.
`IsSteinberg F β` means that for every `a : F` with `a ≠ 0` and `a ≠ 1`,
`β` vanishes on the ordered pair of units induced by `a` and `1 - a`,
both viewed in `Additive Fˣ`. -/
def IsSteinberg {A : Type*} [AddCommGroup A] [Module ℤ A]
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A) : Prop :=
  ∀ (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1),
    β ![Additive.ofMul (Units.mk0 a ha0),
        Additive.ofMul (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm))] = 0

section K2LiftCore

variable {A : Type*} [AddCommGroup A] [Module ℤ A]

/-- Identification of `ι a * ι b` with the `tprod` pure tensor in degree two. -/
private theorem tprod_two_eq_ι_mul_ι (a b : Fˣ) :
    TensorAlgebra.tprod ℤ (Additive Fˣ) 2
        ![Additive.ofMul a, Additive.ofMul b] =
      TensorAlgebra.ι ℤ (Additive.ofMul a) *
        TensorAlgebra.ι ℤ (Additive.ofMul b) := by
  rw [TensorAlgebra.tprod_apply]
  simp

private theorem tensorPairDegree_eq_tprod (a b : Fˣ) :
    tensorPairDegree F a b =
      ⟨TensorAlgebra.tprod ℤ (Additive Fˣ) 2
          ![Additive.ofMul a, Additive.ofMul b],
        TensorAlgebra.tprod_mem_degree 2
          ![Additive.ofMul a, Additive.ofMul b]⟩ := by
  apply Subtype.ext
  exact (tprod_two_eq_ι_mul_ι F a b).symm

/-- `ℤ`-linear lift of a bilinear map to `↥(TensorRing.degree F 2)` via the
general tensor-power identification. -/
noncomputable def degreeK2Lift
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A) :
    ↥(TensorRing.degree F 2) →ₗ[ℤ] A :=
  degreeMultilinearLift F 2 β

/-- Computation: `degreeK2Lift` on `tensorPairDegree` evaluates `β` on the
corresponding pair. -/
@[simp]
theorem degreeK2Lift_tensorPairDegree
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (a b : Fˣ) :
    degreeK2Lift F β (tensorPairDegree F a b) =
      β ![Additive.ofMul a, Additive.ofMul b] := by
  change degreeMultilinearLift F 2 β (tensorPairDegree F a b) = _
  rw [tensorPairDegree_eq_tprod, ← TensorAlgebra.toDegree_tprod,
    degreeMultilinearLift_tprod]

/-- The traditional degree-two Steinberg condition is exactly the adjacent
condition needed by the arbitrary-degree lift. -/
theorem IsSteinberg.isAdjacentSteinberg
    {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A}
    (hβ : IsSteinberg (F := F) β) :
    IsAdjacentSteinberg F 2 β := by
  intro v i hi a ha0 ha1 hv0 hv1
  fin_cases i
  · have hv : v = ![Additive.ofMul (Units.mk0 a ha0),
        Additive.ofMul
          (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm))] := by
      funext j
      fin_cases j
      · exact hv0
      · exact hv1
    rw [hv]
    exact hβ a ha0 ha1
  · simp at hi

/-- A degree-two Steinberg map kills every generator in the generic explicit
Steinberg insertion set, via the arbitrary-degree adjacent criterion. -/
theorem IsSteinberg.isSteinbergInsertVanishing
    {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A}
    (hβ : IsSteinberg (F := F) β) :
    IsSteinbergInsertVanishing F 2 β :=
  hβ.isAdjacentSteinberg.isSteinbergInsertVanishing

/-! ### Textbook presentation kernel lemmas -/

/-- The `ℤ`-linear map `degreeK2Lift` vanishes on the textbook presentation
submodule `steinbergDegreeSpanInDegree F 2`, by the generic span theorem. -/
theorem IsSteinberg.le_ker_steinbergDegreeSpanInDegree
    {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A}
    (hβ : IsSteinberg (F := F) β) :
    steinbergDegreeSpanInDegree F 2 ≤
      LinearMap.ker (degreeK2Lift F β) := by
  exact IsSteinbergInsertVanishing.le_ker_steinbergDegreeSpanInDegree F
    (IsSteinberg.isSteinbergInsertVanishing F hβ)

/-- A bilinear map satisfying the Steinberg relation vanishes on the
degree-two Steinberg submodule, so the submodule lies in the kernel of
`degreeK2Lift`. This is a short structural wrapper around the textbook
presentation kernel lemma via
`steinbergDegreeSubmodule = steinbergDegreeSpanInDegree`. -/
theorem IsSteinberg.le_ker_degreeK2Lift
    {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A}
    (hβ : IsSteinberg (F := F) β) :
    steinbergDegreeSubmodule F 2 ≤
      LinearMap.ker (degreeK2Lift F β) := by
  calc steinbergDegreeSubmodule F 2
      = steinbergDegreeSpanInDegree F 2 :=
        steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree F 2
    _ ≤ LinearMap.ker (degreeK2Lift F β) :=
        hβ.le_ker_steinbergDegreeSpanInDegree

/-- Let `F` be a field and `A` an additive commutative group with a `ℤ`-module
structure. Given a `ℤ`-bilinear map `β` from two copies of `Additive Fˣ` to `A`
and `hβ : IsSteinberg F β`, the lift is a `ℤ`-linear map `MilnorK F 2 →ₗ[ℤ] A`.
On `k2Symbol F a b`, for units `a, b : Fˣ`, it has value
`β ![Additive.ofMul a, Additive.ofMul b]`. -/
noncomputable def liftK2
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (hβ : IsSteinberg (F := F) β) :
    MilnorK F 2 →ₗ[ℤ] A :=
  liftDegreeOfAdjacentSteinberg F 2 β hβ.isAdjacentSteinberg

/-- Computation for `liftK2` on `mk`. -/
@[simp]
theorem liftK2_mk
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (hβ : IsSteinberg (F := F) β)
    (x : ↥(TensorRing.degree F 2)) :
    liftK2 F β hβ (mk F 2 x) = degreeK2Lift F β x := by
  exact liftDegreeOfAdjacentSteinberg_mk F 2 β
    hβ.isAdjacentSteinberg x

/-- Computation on the canonical degree-two pair `tensorPairDegree`. -/
@[simp]
theorem liftK2_tensorPairDegree
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (hβ : IsSteinberg (F := F) β)
    (a b : Fˣ) :
    liftK2 F β hβ (mk F 2 (tensorPairDegree F a b)) =
      β ![Additive.ofMul a, Additive.ofMul b] := by
  rw [liftK2_mk, degreeK2Lift_tensorPairDegree]

/-- `k2Symbol` is the `mk` of the canonical degree-two pair, proved directly
in `MilnorK F 2 = MilnorKRing.degree F 2`. -/
theorem k2Symbol_eq_mk_tensorPairDegree (a b : Fˣ) :
    k2Symbol F a b = mk F 2 (tensorPairDegree F a b) := by
  apply Subtype.ext
  calc (k2Symbol F a b : MilnorKRing F)
      = MilnorKRing.k2Symbol (F := F) a b := rfl
    _ = MilnorKRing.symbol F a * MilnorKRing.symbol F b := rfl
    _ = MilnorKRing.mk F (TensorAlgebra.ι ℤ (Additive.ofMul a)) *
          MilnorKRing.mk F (TensorAlgebra.ι ℤ (Additive.ofMul b)) := rfl
    _ = MilnorKRing.mk F
          (TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)) := by
        rw [← map_mul]
    _ = MilnorKRing.mkLinear F
          (TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)) := rfl
    _ = MilnorKRing.mkLinear F (tensorPairDegree F a b : TensorRing F) := by
        rw [tensorPairDegree_coe]
    _ = (mk F 2 (tensorPairDegree F a b) : MilnorKRing F) := by
        rw [← mk_coe]

/-- Computation on `k2Symbol`. -/
@[simp]
theorem liftK2_k2Symbol
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (hβ : IsSteinberg (F := F) β)
    (a b : Fˣ) :
    liftK2 F β hβ (k2Symbol F a b) =
      β ![Additive.ofMul a, Additive.ofMul b] := by
  calc liftK2 F β hβ (k2Symbol F a b)
      = liftK2 F β hβ (mk F 2 (tensorPairDegree F a b)) := by
        rw [k2Symbol_eq_mk_tensorPairDegree]
    _ = β ![Additive.ofMul a, Additive.ofMul b] := by
        rw [liftK2_tensorPairDegree]

/-- Two universal `K₂` lifts agreeing on pure symbol pairs are equal. -/
theorem liftK2_ext
    (β₁ β₂ : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A)
    (h₁ : IsSteinberg (F := F) β₁)
    (h₂ : IsSteinberg (F := F) β₂)
    (h_eq : ∀ a b : Fˣ,
      β₁ ![Additive.ofMul a, Additive.ofMul b] =
      β₂ ![Additive.ofMul a, Additive.ofMul b]) :
    liftK2 F β₁ h₁ = liftK2 F β₂ h₂ := by
  apply k2Symbol_ext
  intro a b
  rw [liftK2_k2Symbol, liftK2_k2Symbol, h_eq]

end K2LiftCore

/-! ### Bundled separately multiplicative Steinberg bimap -/

/-- For a field `F` and an additive commutative group `A`, a Steinberg bimap
is a function `Fˣ → Fˣ → A` that sends multiplication in each argument
to addition in `A` with the other argument fixed. For every `a : F`
with `a ≠ 0` and `a ≠ 1`, it vanishes on the ordered pair of units
induced by `a` and `1 - a`. -/
structure SteinbergBimap (F : Type*) (A : Type*) [Field F] [AddCommGroup A] where
  /-- Underlying function `Fˣ → Fˣ → A`. -/
  toFun : Fˣ → Fˣ → A
  /-- Multiplicative in the first argument, additive in the target. -/
  map_mul_left : ∀ (a₁ a₂ b : Fˣ), toFun (a₁ * a₂) b = toFun a₁ b + toFun a₂ b
  /-- Multiplicative in the second argument, additive in the target. -/
  map_mul_right : ∀ (a b₁ b₂ : Fˣ), toFun a (b₁ * b₂) = toFun a b₁ + toFun a b₂
  /-- Vanishes on every Steinberg pair `a, 1-a`. -/
  steinberg : ∀ (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1),
      toFun (Units.mk0 a ha0) (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 0

namespace SteinbergBimap

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A]

/-- `SteinbergBimap` is callable as `Fˣ → Fˣ → A`. -/
instance instCoeFunSteinbergBimap :
    CoeFun (SteinbergBimap F A) (fun _ => Fˣ → Fˣ → A) where
  coe b := b.toFun

@[simp]
theorem coe_toFun (b : SteinbergBimap F A) : (b.toFun : Fˣ → Fˣ → A) = ⇑b :=
  rfl

theorem coe_eq_toFun (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    b a₁ a₂ = b.toFun a₁ a₂ :=
  rfl

/-- Extensionality: two bimaps coincide if their underlying functions coincide. -/
theorem ext {b₁ b₂ : SteinbergBimap F A}
    (h : ∀ a₁ a₂ : Fˣ, b₁ a₁ a₂ = b₂ a₁ a₂) : b₁ = b₂ := by
  cases b₁ with
  | mk f₁ h₁₁ h₁₂ h₁₃ =>
    cases b₂ with
    | mk f₂ h₂₁ h₂₂ h₂₃ =>
      have hf : f₁ = f₂ := by
        funext a₁ a₂
        exact h a₁ a₂
      subst hf
      rfl

/-- Vanishing at `1` in the first argument. -/
theorem map_one_left (b : SteinbergBimap F A) (x : Fˣ) : b (1 : Fˣ) x = 0 := by
  have h_eq : b.toFun (1 : Fˣ) x = b.toFun (1 : Fˣ) x + b.toFun (1 : Fˣ) x := by
    calc b.toFun (1 : Fˣ) x = b.toFun ((1 : Fˣ) * 1) x := by rw [mul_one]
      _ = b.toFun (1 : Fˣ) x + b.toFun (1 : Fˣ) x := b.map_mul_left 1 1 x
  have h_add : b.toFun (1 : Fˣ) x + 0 = b.toFun (1 : Fˣ) x + b.toFun (1 : Fˣ) x := by
    calc b.toFun (1 : Fˣ) x + 0 = b.toFun (1 : Fˣ) x := by rw [add_zero]
      _ = b.toFun (1 : Fˣ) x + b.toFun (1 : Fˣ) x := h_eq
  have h_zero : (0 : A) = b.toFun (1 : Fˣ) x := add_left_cancel h_add
  exact h_zero.symm

/-- Vanishing at `1` in the second argument. -/
theorem map_one_right (b : SteinbergBimap F A) (x : Fˣ) : b x (1 : Fˣ) = 0 := by
  have h_eq : b.toFun x (1 : Fˣ) = b.toFun x (1 : Fˣ) + b.toFun x (1 : Fˣ) := by
    calc b.toFun x (1 : Fˣ) = b.toFun x ((1 : Fˣ) * 1) := by rw [mul_one]
      _ = b.toFun x (1 : Fˣ) + b.toFun x (1 : Fˣ) := b.map_mul_right x 1 1
  have h_add : b.toFun x (1 : Fˣ) + 0 = b.toFun x (1 : Fˣ) + b.toFun x (1 : Fˣ) := by
    calc b.toFun x (1 : Fˣ) + 0 = b.toFun x (1 : Fˣ) := by rw [add_zero]
      _ = b.toFun x (1 : Fˣ) + b.toFun x (1 : Fˣ) := h_eq
  have h_zero : (0 : A) = b.toFun x (1 : Fˣ) := add_left_cancel h_add
  exact h_zero.symm

/-- Inverse in the first argument gives negation. -/
theorem map_inv_left (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    b a₁⁻¹ a₂ = -b a₁ a₂ := by
  have h_one : b.toFun (1 : Fˣ) a₂ = 0 := b.map_one_left a₂
  have h_mul : b.toFun (a₁ * a₁⁻¹) a₂ = b.toFun a₁ a₂ + b.toFun a₁⁻¹ a₂ :=
    b.map_mul_left a₁ a₁⁻¹ a₂
  have h_eq : (0 : A) = b.toFun a₁ a₂ + b.toFun a₁⁻¹ a₂ := by
    rw [mul_inv_cancel] at h_mul
    rw [← h_mul, h_one]
  calc b.toFun a₁⁻¹ a₂ = 0 + b.toFun a₁⁻¹ a₂ := by rw [zero_add]
    _ = -b.toFun a₁ a₂ + b.toFun a₁ a₂ + b.toFun a₁⁻¹ a₂ := by
        rw [neg_add_cancel, zero_add]
    _ = -b.toFun a₁ a₂ + (b.toFun a₁ a₂ + b.toFun a₁⁻¹ a₂) := by
        rw [add_assoc]
    _ = -b.toFun a₁ a₂ + 0 := by rw [← h_eq]
    _ = -b.toFun a₁ a₂ := by rw [add_zero]

/-- Inverse in the second argument gives negation. -/
theorem map_inv_right (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    b a₁ a₂⁻¹ = -b a₁ a₂ := by
  have h_one : b.toFun a₁ (1 : Fˣ) = 0 := b.map_one_right a₁
  have h_mul : b.toFun a₁ (a₂ * a₂⁻¹) = b.toFun a₁ a₂ + b.toFun a₁ a₂⁻¹ :=
    b.map_mul_right a₁ a₂ a₂⁻¹
  have h_eq : (0 : A) = b.toFun a₁ a₂ + b.toFun a₁ a₂⁻¹ := by
    rw [mul_inv_cancel] at h_mul
    rw [← h_mul, h_one]
  calc b.toFun a₁ a₂⁻¹ = 0 + b.toFun a₁ a₂⁻¹ := by rw [zero_add]
    _ = -b.toFun a₁ a₂ + b.toFun a₁ a₂ + b.toFun a₁ a₂⁻¹ := by
        rw [neg_add_cancel, zero_add]
    _ = -b.toFun a₁ a₂ + (b.toFun a₁ a₂ + b.toFun a₁ a₂⁻¹) := by
        rw [add_assoc]
    _ = -b.toFun a₁ a₂ + 0 := by rw [← h_eq]
    _ = -b.toFun a₁ a₂ := by rw [add_zero]

private def leftMulHom (b : SteinbergBimap F A) (y : Fˣ) : Fˣ →* Multiplicative A where
  toFun x := Multiplicative.ofAdd (b.toFun x y)
  map_one' := by
    rw [b.map_one_left y, ofAdd_zero]
  map_mul' := by
    intro x₁ x₂
    rw [b.map_mul_left x₁ x₂ y, ofAdd_add]

private def rightMulHom (b : SteinbergBimap F A) (x : Fˣ) : Fˣ →* Multiplicative A where
  toFun y := Multiplicative.ofAdd (b.toFun x y)
  map_one' := by
    rw [b.map_one_right x, ofAdd_zero]
  map_mul' := by
    intro y₁ y₂
    rw [b.map_mul_right x y₁ y₂, ofAdd_add]

/-- `ℤ`-power in the first argument. -/
theorem map_zpow_left (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) (n : ℤ) :
    b (a₁ ^ n) a₂ = n • b a₁ a₂ := by
  have h_zpow :
      (leftMulHom b a₂) (a₁ ^ n) = (leftMulHom b a₂ a₁) ^ n :=
    MonoidHom.map_zpow (leftMulHom b a₂) a₁ n
  have h_ofAdd : Multiplicative.ofAdd (b.toFun (a₁ ^ n) a₂) =
      (Multiplicative.ofAdd (b.toFun a₁ a₂) : Multiplicative A) ^ n := h_zpow
  have h_eq : Multiplicative.ofAdd (b.toFun (a₁ ^ n) a₂) =
      Multiplicative.ofAdd (n • b.toFun a₁ a₂) := by
    rw [h_ofAdd, ofAdd_zsmul]
  have h_toAdd : (Multiplicative.ofAdd (b.toFun (a₁ ^ n) a₂) : Multiplicative A).toAdd =
      (Multiplicative.ofAdd (n • b.toFun a₁ a₂) : Multiplicative A).toAdd := by
    rw [h_eq]
  simpa only [toAdd_ofAdd] using h_toAdd

/-- `ℤ`-power in the second argument. -/
theorem map_zpow_right (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) (n : ℤ) :
    b a₁ (a₂ ^ n) = n • b a₁ a₂ := by
  have h_zpow :
      (rightMulHom b a₁) (a₂ ^ n) = (rightMulHom b a₁ a₂) ^ n :=
    MonoidHom.map_zpow (rightMulHom b a₁) a₂ n
  have h_ofAdd : Multiplicative.ofAdd (b.toFun a₁ (a₂ ^ n)) =
      (Multiplicative.ofAdd (b.toFun a₁ a₂) : Multiplicative A) ^ n := h_zpow
  have h_eq : Multiplicative.ofAdd (b.toFun a₁ (a₂ ^ n)) =
      Multiplicative.ofAdd (n • b.toFun a₁ a₂) := by
    rw [h_ofAdd, ofAdd_zsmul]
  have h_toAdd : (Multiplicative.ofAdd (b.toFun a₁ (a₂ ^ n)) : Multiplicative A).toAdd =
      (Multiplicative.ofAdd (n • b.toFun a₁ a₂) : Multiplicative A).toAdd := by
    rw [h_eq]
  simpa only [toAdd_ofAdd] using h_toAdd

/-- Conversion to `MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A`.

This encapsulates the linearity boilerplate previously repeated in
`Ring/K2/MilnorComparison.lean`. -/
noncomputable def toMultilinearMap (b : SteinbergBimap F A) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin 2 => Additive Fˣ) A :=
  MultilinearMap.mk'
    (fun m => b.toFun (Additive.toMul (m 0)) (Additive.toMul (m 1)))
    (by
      intro m i x y
      fin_cases i
      · simp [toMul_add, b.map_mul_left]
      · simp [toMul_add, b.map_mul_right])
    (by
      intro m i c x
      fin_cases i
      · simp [toMul_zsmul, b.map_zpow_left]
      · simp [toMul_zsmul, b.map_zpow_right])

/-- The multilinear map evaluates the bundled function. -/
@[simp]
theorem toMultilinearMap_apply (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    b.toMultilinearMap ![Additive.ofMul a₁, Additive.ofMul a₂] =
      b.toFun a₁ a₂ :=
  rfl

/-- The multilinear map satisfies the Steinberg relation. -/
theorem isSteinberg_toMultilinearMap (b : SteinbergBimap F A) :
    IsSteinberg (F := F) b.toMultilinearMap := by
  intro a ha0 ha1
  simp only [toMultilinearMap_apply, b.steinberg a ha0 ha1]

/-- Postcomposition with a `ℤ`-linear map preserves the bimap structure. -/
def compLinearMap {B : Type*} [AddCommGroup B]
    (b : SteinbergBimap F A) (f : A →ₗ[ℤ] B) : SteinbergBimap F B where
  toFun a₁ a₂ := f (b.toFun a₁ a₂)
  map_mul_left a₁ a₂ b₁ := by
    rw [b.map_mul_left a₁ a₂ b₁, map_add]
  map_mul_right a b₁ b₂ := by
    rw [b.map_mul_right a b₁ b₂, map_add]
  steinberg a ha0 ha1 := by
    rw [b.steinberg a ha0 ha1, map_zero]

/-- Postcomposition evaluates via the linear map. -/
@[simp]
theorem compLinearMap_apply {B : Type*} [AddCommGroup B]
    (b : SteinbergBimap F A) (f : A →ₗ[ℤ] B) (a₁ a₂ : Fˣ) :
    (b.compLinearMap f).toFun a₁ a₂ = f (b.toFun a₁ a₂) :=
  rfl

/-- `toMultilinearMap` commutes with postcomposition. -/
theorem toMultilinearMap_compLinearMap {B : Type*} [AddCommGroup B]
    (b : SteinbergBimap F A) (f : A →ₗ[ℤ] B) :
    (b.compLinearMap f).toMultilinearMap =
      f.compMultilinearMap b.toMultilinearMap := by
  ext m
  have h_eq : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h_eq]
  rfl

end SteinbergBimap

section BimapLift

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A]

/-- Universal lift from a bundled Steinberg bimap to `MilnorK F 2`.

Implemented through the existing `liftK2` via `toMultilinearMap`. -/
noncomputable def liftK2OfBimap (b : SteinbergBimap F A) :
    MilnorK F 2 →ₗ[ℤ] A :=
  liftK2 F b.toMultilinearMap b.isSteinberg_toMultilinearMap

/-- Alias for `liftK2OfBimap`, emphasizing bicharacter language. -/
noncomputable abbrev liftK2OfBicharacter (b : SteinbergBimap F A) :
    MilnorK F 2 →ₗ[ℤ] A :=
  liftK2OfBimap b

/-- Computation on `k2Symbol`: the lift evaluates the underlying bimap. -/
@[simp]
theorem liftK2OfBimap_k2Symbol (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    liftK2OfBimap b (k2Symbol F a₁ a₂) = b.toFun a₁ a₂ := by
  unfold liftK2OfBimap
  rw [liftK2_k2Symbol]
  exact SteinbergBimap.toMultilinearMap_apply b a₁ a₂

/-- Computation on the canonical `mk` of a pure tensor pair. -/
@[simp]
theorem liftK2OfBimap_mk_tensorPairDegree (b : SteinbergBimap F A) (a₁ a₂ : Fˣ) :
    liftK2OfBimap b (mk F 2 (tensorPairDegree F a₁ a₂)) = b.toFun a₁ a₂ := by
  calc liftK2OfBimap b (mk F 2 (tensorPairDegree F a₁ a₂))
      = liftK2OfBimap b (k2Symbol F a₁ a₂) := by
        rw [k2Symbol_eq_mk_tensorPairDegree]
    _ = b.toFun a₁ a₂ := liftK2OfBimap_k2Symbol b a₁ a₂

/-- Computation on a general `mk`. -/
@[simp]
theorem liftK2OfBimap_mk (b : SteinbergBimap F A)
    (x : ↥(TensorRing.degree F 2)) :
    liftK2OfBimap b (mk F 2 x) = degreeK2Lift F b.toMultilinearMap x := by
  simp [liftK2OfBimap]

/-- Functoriality: postcomposing the bimap commutes with the lift. -/
theorem liftK2OfBimap_comp {B : Type*} [AddCommGroup B]
    (b : SteinbergBimap F A) (f : A →ₗ[ℤ] B) :
    liftK2OfBimap (b.compLinearMap f) = f.comp (liftK2OfBimap b) := by
  unfold liftK2OfBimap liftK2
  let hbase := IsSteinberg.isAdjacentSteinberg F
    b.isSteinberg_toMultilinearMap
  let hcomp := IsAdjacentSteinberg.compLinearMap F hbase f
  calc
    liftDegreeOfAdjacentSteinberg F 2
          (b.compLinearMap f).toMultilinearMap _ =
        liftDegreeOfAdjacentSteinberg F 2
          (f.compMultilinearMap b.toMultilinearMap) hcomp :=
      liftDegreeOfAdjacentSteinberg_congr F 2 _ _ _ _
        (SteinbergBimap.toMultilinearMap_compLinearMap b f)
    _ = f.comp
        (liftDegreeOfAdjacentSteinberg F 2 b.toMultilinearMap hbase) :=
      liftDegreeOfAdjacentSteinberg_compLinearMap F 2
        b.toMultilinearMap hbase f

/-- Two lifts from bimaps agreeing on all pairs are equal. -/
theorem liftK2OfBimap_ext (b₁ b₂ : SteinbergBimap F A)
    (h : ∀ a₁ a₂ : Fˣ, b₁.toFun a₁ a₂ = b₂.toFun a₁ a₂) :
    liftK2OfBimap b₁ = liftK2OfBimap b₂ := by
  apply k2Symbol_ext
  intro a₁ a₂
  rw [liftK2OfBimap_k2Symbol, liftK2OfBimap_k2Symbol, h]

/-- Extensionality for `liftK2OfBimap` via equality of bimaps. -/
theorem liftK2OfBimap_congr (b₁ b₂ : SteinbergBimap F A)
    (h : b₁ = b₂) : liftK2OfBimap b₁ = liftK2OfBimap b₂ := by
  subst h
  rfl

end BimapLift

end MilnorK
