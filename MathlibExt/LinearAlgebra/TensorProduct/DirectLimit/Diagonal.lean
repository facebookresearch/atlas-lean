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

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.Order.DirectedInverseSystem

/-!
# Mixed-stage tensor maps for direct-limit diagonals

The maps use module direct limits and tensor maps. Changing the common
upper stage preserves the represented tensor.
Transition injectivity and flatness are not required.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe r i m n

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {M : ι → Type m} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
  {N : ι → Type n} [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]
  (f : ∀ a b, a ≤ b → M a →ₗ[R] M b)
  (g : ∀ a b, a ≤ b → N a →ₗ[R] N b)

/-- The simultaneous transition is the actual native tensor map. -/
def diagonalTransition (a b : ι) (h : a ≤ b) :
    M a ⊗[R] N a →ₗ[R] M b ⊗[R] N b :=
  TensorProduct.map (f a b h) (g a b h)

/-- The native module direct limit of simultaneous tensor stages. -/
abbrev diagonalLimit :=
  Module.DirectLimit (fun j => M j ⊗[R] N j) (diagonalTransition f g)

/-- Push a mixed-stage tensor to an actual common upper stage and take its
native module-colimit class. -/
def diagonalStageAt (a b c : ι) (ha : a ≤ c) (hb : b ≤ c) :
    M a ⊗[R] N b →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
    (diagonalTransition f g) c).comp (TensorProduct.map (f a c ha) (g b c hb))

@[simp]
theorem diagonalStageAt_tmul (a b c : ι) (ha : a ≤ c) (hb : b ≤ c)
    (x : M a) (y : N b) :
    diagonalStageAt f g a b c ha hb (x ⊗ₜ[R] y) =
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
        (diagonalTransition f g) c (f a c ha x ⊗ₜ[R] g b c hb y) := by
  simp only [diagonalStageAt, LinearMap.comp_apply, TensorProduct.map_tmul]

variable [DirectedSystem M (f · · ·)] [DirectedSystem N (g · · ·)]

omit [DecidableEq ι] in
/-- The actual simultaneous tensor transitions form a directed system.
Only the original preorder and factor-system laws are needed. -/
instance diagonalDirectedSystem :
    DirectedSystem (fun a => M a ⊗[R] N a) (diagonalTransition f g · · ·) where
  map_self a z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [diagonalTransition, TensorProduct.map_tmul,
          DirectedSystem.map_self' f, DirectedSystem.map_self' g]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_map {c b a} hab hbc z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [diagonalTransition, TensorProduct.map_tmul,
          DirectedSystem.map_map' f hab hbc, DirectedSystem.map_map' g hab hbc]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Raising the common upper stage gives the same actual class. -/
theorem diagonalStageAt_mono (a b c d : ι) (ha : a ≤ c) (hb : b ≤ c)
    (h : c ≤ d) :
    diagonalStageAt f g a b c ha hb =
      diagonalStageAt f g a b d (ha.trans h) (hb.trans h) := by
  apply TensorProduct.ext'
  intro x y
  rw [diagonalStageAt_tmul, diagonalStageAt_tmul]
  have he := Module.DirectLimit.of_f
    (R := R) (ι := ι) (G := fun j => M j ⊗[R] N j)
    (f := diagonalTransition f g) (i := c) (j := d) (hij := h)
    (x := f a c ha x ⊗ₜ[R] g b c hb y)
  simp only [diagonalTransition, TensorProduct.map_tmul,
    DirectedSystem.map_map' f, DirectedSystem.map_map' g] at he
  exact he.symm

variable [IsDirectedOrder ι]

/-- Independence of the chosen upper stage follows from an actual further
common upper stage and directed-system composition. -/
theorem diagonalStageAt_eq (a b c d : ι) (ha : a ≤ c) (hb : b ≤ c)
    (ha' : a ≤ d) (hb' : b ≤ d) :
    diagonalStageAt f g a b c ha hb = diagonalStageAt f g a b d ha' hb' := by
  obtain ⟨e, hc, hd⟩ := exists_ge_ge c d
  exact (diagonalStageAt_mono f g a b c e ha hb hc).trans
    (diagonalStageAt_mono f g a b d e ha' hb' hd).symm


/-- The canonical mixed-stage map uses an actual common upper stage. Its value
is independent of that choice by diagonalStageAt_eq. -/
def diagonalStage (a b : ι) : M a ⊗[R] N b →ₗ[R] diagonalLimit f g :=
  let h := exists_ge_ge a b
  diagonalStageAt f g a b (Classical.choose h)
    (Classical.choose_spec h).1 (Classical.choose_spec h).2

theorem diagonalStage_eq (a b c : ι) (ha : a ≤ c) (hb : b ≤ c) :
    diagonalStage f g a b = diagonalStageAt f g a b c ha hb := by
  let h := exists_ge_ge a b
  exact diagonalStageAt_eq f g a b (Classical.choose h) c
    (Classical.choose_spec h).1 (Classical.choose_spec h).2 ha hb

/-- Compatibility with the actual transition in the second tensor factor. -/
theorem diagonalStage_comp_right (a b c : ι) (h : b ≤ c) :
    (diagonalStage f g a c).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (g b c h)) =
      diagonalStage f g a b := by
  obtain ⟨d, ha, hc⟩ := exists_ge_ge a c
  rw [diagonalStage_eq f g a c d ha hc, diagonalStage_eq f g a b d ha (h.trans hc)]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    diagonalStageAt_tmul, DirectedSystem.map_map' g]

/-- Compatibility with the actual transition in the first tensor factor. -/
theorem diagonalStage_comp_left (a b c : ι) (h : a ≤ c) :
    (diagonalStage f g c b).comp
        (TensorProduct.map (f a c h) (LinearMap.id : N b →ₗ[R] N b)) =
      diagonalStage f g a b := by
  obtain ⟨d, hc, hb⟩ := exists_ge_ge c b
  rw [diagonalStage_eq f g c b d hc hb, diagonalStage_eq f g a b d (h.trans hc) hb]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    diagonalStageAt_tmul, DirectedSystem.map_map' f]

/-- At an actual diagonal stage the canonical mixed-stage map is the native
stage injection, rather than a caller-supplied inverse formula. -/
theorem diagonalStage_self (a : ι) :
    diagonalStage f g a a =
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j) (diagonalTransition f g) a := by
  rw [diagonalStage_eq f g a a a le_rfl le_rfl]
  apply TensorProduct.ext'
  intro x y
  simp only [diagonalStageAt_tmul, DirectedSystem.map_self' f, DirectedSystem.map_self' g]


omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
/-- The actual forward diagonal comparison is the native module-colimit lift
of the simultaneous stage injections into the two factor colimits. -/
def diagonalToTensor :
    diagonalLimit f g →ₗ[R] Module.DirectLimit M f ⊗[R] Module.DirectLimit N g :=
  Module.DirectLimit.lift R ι (fun j => M j ⊗[R] N j) (diagonalTransition f g)
    (fun j => TensorProduct.map (Module.DirectLimit.of R ι M f j)
      (Module.DirectLimit.of R ι N g j)) (by
      intro a b h z
      have he :
          (TensorProduct.map (Module.DirectLimit.of R ι M f b)
              (Module.DirectLimit.of R ι N g b)).comp (diagonalTransition f g a b h) =
            TensorProduct.map (Module.DirectLimit.of R ι M f a)
              (Module.DirectLimit.of R ι N g a) := by
        apply TensorProduct.ext'
        intro x y
        simp only [LinearMap.comp_apply, diagonalTransition, TensorProduct.map_tmul,
          Module.DirectLimit.of_f]
      exact LinearMap.congr_fun he z)

omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
/-- The whole forward stage tensor uses the native factor injections.
This characteristic needs no directedness or directed-system laws. -/
@[simp]
theorem diagonalToTensor_of (a : ι) (z : M a ⊗[R] N a) :
    diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a z) =
      TensorProduct.map (Module.DirectLimit.of R ι M f a)
        (Module.DirectLimit.of R ι N g a) z := by
  simp only [diagonalToTensor, Module.DirectLimit.lift_of]

omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
theorem diagonalToTensor_of_tmul (a : ι) (x : M a) (y : N a) :
    diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g a y := by
  rw [diagonalToTensor_of, TensorProduct.map_tmul]

/-- Native tensor/direct-limit commutation in the second factor followed by
the computed mixed-stage lift. -/
def diagonalSecond (a : ι) :
    M a ⊗[R] Module.DirectLimit N g →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.lift R ι (fun b => M a ⊗[R] N b)
    (fun b c h => LinearMap.lTensor (M a) (g b c h))
    (fun b => diagonalStage f g a b) (by
      intro b c h z
      exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)).comp
    (TensorProduct.directLimitRight g (M a)).toLinearMap

@[simp]
theorem diagonalSecond_tmul_of (a b : ι) (x : M a) (y : N b) :
    diagonalSecond f g a (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
  let p : Module.DirectLimit (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h)) →ₗ[R] diagonalLimit f g :=
    Module.DirectLimit.lift R ι (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h))
      (fun b => diagonalStage f g a b) (by
        intro b c h z
        exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)
  change p (TensorProduct.directLimitRight g (M a)
    (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) = _
  have he := TensorProduct.directLimitRight_tmul_of (f := g) (M := M a) (i := b) x y
  have hp : p (Module.DirectLimit.of R ι (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h)) b (x ⊗ₜ[R] y)) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
    exact Module.DirectLimit.lift_of (R := R) (ι := ι)
      (G := fun b => M a ⊗[R] N b)
      (f := fun b c h => LinearMap.lTensor (M a) (g b c h))
      (fun b => diagonalStage f g a b) (by
        intro b c h z
        exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)
      (i := b) (x ⊗ₜ[R] y)
  exact (congrArg p he).trans hp

/-- The second-factor lift respects the actual first-factor transition. -/
theorem diagonalSecond_comp (a c : ι) (h : a ≤ c) :
    (diagonalSecond f g c).comp (LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) =
      diagonalSecond f g a := by
  apply TensorProduct.ext'
  intro x z
  have hx :
      TensorProduct.curry
          ((diagonalSecond f g c).comp
            (LinearMap.rTensor (Module.DirectLimit N g) (f a c h))) x =
        TensorProduct.curry (diagonalSecond f g a) x := by
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := N) (f := g)
    intro b
    apply LinearMap.ext
    intro y
    change diagonalSecond f g c
        (f a c h x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalSecond f g a (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)
    rw [diagonalSecond_tmul_of, diagonalSecond_tmul_of]
    exact LinearMap.congr_fun (diagonalStage_comp_left f g a b c h) (x ⊗ₜ[R] y)
  exact LinearMap.congr_fun hx z

/-- The inverse candidate uses native single-moving-factor equivalences and
module-colimit lifts, with both transition compatibilities already earned. -/
def tensorToDiagonal :
    Module.DirectLimit M f ⊗[R] Module.DirectLimit N g →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.lift R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
    (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h))
    (fun a => diagonalSecond f g a) (by
      intro a c h z
      exact LinearMap.congr_fun (diagonalSecond_comp f g a c h) z)).comp
    (TensorProduct.directLimitLeft f (Module.DirectLimit N g)).toLinearMap

/-- Its mixed-stage characteristic is the actual common-stage tensor class. -/
@[simp]
theorem tensorToDiagonal_of_tmul_of (a b : ι) (x : M a) (y : N b) :
    tensorToDiagonal f g
        (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
  let p : Module.DirectLimit (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) →ₗ[R]
        diagonalLimit f g :=
    Module.DirectLimit.lift R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h))
      (fun a => diagonalSecond f g a) (by
        intro a c h z
        exact LinearMap.congr_fun (diagonalSecond_comp f g a c h) z)
  change p (TensorProduct.directLimitLeft f (Module.DirectLimit N g)
    (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) = _
  have he := TensorProduct.directLimitLeft_tmul_of (f := f)
    (M := Module.DirectLimit N g) (i := a) x (Module.DirectLimit.of R ι N g b y)
  have hp : p (Module.DirectLimit.of R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) a
        (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
    simp only [p, Module.DirectLimit.lift_of, diagonalSecond_tmul_of]
  exact (congrArg p he).trans hp


/-- The computed forward map sends a mixed-stage tensor to its two native
factor classes, independently of the common upper stage. -/
theorem diagonalToTensor_diagonalStage (a b : ι) (x : M a) (y : N b) :
    diagonalToTensor f g (diagonalStage f g a b (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y := by
  obtain ⟨c, ha, hb⟩ := exists_ge_ge a b
  rw [diagonalStage_eq f g a b c ha hb, diagonalStageAt_tmul,
    diagonalToTensor_of_tmul, Module.DirectLimit.of_f, Module.DirectLimit.of_f]

/-- The inverse candidate followed by the forward map is identity on the
actual factor-colimit tensor product. -/
theorem diagonalToTensor_comp_tensorToDiagonal :
    (diagonalToTensor f g).comp (tensorToDiagonal f g) = LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  have he :
      TensorProduct.curry ((diagonalToTensor f g).comp (tensorToDiagonal f g)) =
        TensorProduct.curry
          (LinearMap.id : Module.DirectLimit M f ⊗[R] Module.DirectLimit N g →ₗ[R]
            Module.DirectLimit M f ⊗[R] Module.DirectLimit N g) := by
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := M) (f := f)
    intro a
    apply LinearMap.ext
    intro u
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := N) (f := g)
    intro b
    apply LinearMap.ext
    intro v
    change diagonalToTensor f g
        (tensorToDiagonal f g
          (Module.DirectLimit.of R ι M f a u ⊗ₜ[R] Module.DirectLimit.of R ι N g b v)) =
      Module.DirectLimit.of R ι M f a u ⊗ₜ[R] Module.DirectLimit.of R ι N g b v
    rw [tensorToDiagonal_of_tmul_of, diagonalToTensor_diagonalStage]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- The forward map followed by the inverse is identity on the actual
simultaneous-stage module quotient. -/
theorem tensorToDiagonal_comp_diagonalToTensor :
    (tensorToDiagonal f g).comp (diagonalToTensor f g) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext (R := R) (ι := ι)
    (G := fun j => M j ⊗[R] N j) (f := diagonalTransition f g)
  intro a
  apply TensorProduct.ext'
  intro x y
  change tensorToDiagonal f g
      (diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y))) =
    Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
      (diagonalTransition f g) a (x ⊗ₜ[R] y)
  rw [diagonalToTensor_of_tmul, tensorToDiagonal_of_tmul_of, diagonalStage_self]

/-- The canonical unbundled diagonal tensor/direct-limit equivalence.
The index, scalar and both module worlds are independent; no transition
injectivity, flatness, field or supplied inverse is assumed. -/
def directLimitDiagonal :
    diagonalLimit f g ≃ₗ[R] Module.DirectLimit M f ⊗[R] Module.DirectLimit N g :=
  LinearEquiv.ofLinearMap (diagonalToTensor f g) (tensorToDiagonal f g)
    (diagonalToTensor_comp_tensorToDiagonal f g)
    (tensorToDiagonal_comp_diagonalToTensor f g)

/-- The whole stage tensor maps by the exact native injections of its factors. -/
@[simp]
theorem directLimitDiagonal_of (a : ι) (z : M a ⊗[R] N a) :
    directLimitDiagonal f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a z) =
      TensorProduct.map (Module.DirectLimit.of R ι M f a)
        (Module.DirectLimit.of R ι N g a) z := by
  exact diagonalToTensor_of f g a z

/-- The forward characteristic retains exactly the native simultaneous stage map. -/
theorem directLimitDiagonal_of_tmul (a : ι) (x : M a) (y : N a) :
    directLimitDiagonal f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g a y :=
  diagonalToTensor_of_tmul f g a x y

/-- The inverse characteristic is the computed class at any actual common stage. -/
@[simp]
theorem directLimitDiagonal_symm_of_tmul_of (a b : ι) (x : M a) (y : N b) :
    (directLimitDiagonal f g).symm
        (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) :=
  tensorToDiagonal_of_tmul_of f g a b x y

/-- A stage tensor whose two factor classes give zero is killed at an actual
common later stage. This uses only additive monoids over a commutative semiring;
the supplied stage removes any need for a nonempty-index assumption. -/
theorem exists_eq_zero_of_map_to_directLimit_diagonal_eq_zero
    {a : ι} (z : M a ⊗[R] N a)
    (hz : TensorProduct.map (Module.DirectLimit.of R ι M f a)
      (Module.DirectLimit.of R ι N g a) z = 0) :
    ∃ c : ι, ∃ h : a ≤ c,
      TensorProduct.map (f a c h) (g a c h) z = 0 := by
  have hcolimit :
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
        (diagonalTransition f g) a z = 0 := by
    apply (directLimitDiagonal f g).injective
    rw [directLimitDiagonal_of, map_zero]
    exact hz
  exact Module.DirectLimit.of.zero_exact hcolimit

end TensorProduct
