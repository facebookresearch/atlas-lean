/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Basic
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence
public import MathlibExt.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.Functor

/-!
# Coefficient and algebra maps of Hochschild complexes

Tensor maps induce Hochschild chain maps when the coefficient map
intertwines both actions. Algebra maps may be nonunital: preservation of
addition, ground scalars and multiplication suffices for the boundary
squares. The ground ring, algebra and coefficient carrier universes are
independent. Universe lifting gives chain and homology maps in a common
module category.

Reference: Loday, Cyclic Homology, second edition, §1.1.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v v' v'' w w' w'' z t s

namespace ModuleCat.Algebra.Hochschild

attribute [local instance] uliftSMulCommClass

section TensorMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]
  {P : Type w''} [AddCommGroup P] [Module k P]

/-- The tensor map, with independent coefficient and algebra universes. -/
def linearMap (g : A →ₙₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] N ⊗[k] TensorPower k n B :=
  TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => (g : A →ₗ[k] B)))

@[simp]
theorem linearMap_tprod (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (n : ℕ) (m : M) (a : Fin n → A) :
    linearMap g f n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) := by
  simp only [linearMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

@[simp]
theorem linearMap_id (n : ℕ) :
    linearMap (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = LinearMap.id := by
  apply tensorPower_ext
  intro m a
  rw [linearMap_tprod]
  rfl

theorem linearMap_comp (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P) (n : ℕ) :
    (linearMap h f' n).comp (linearMap g f n) =
      linearMap (h.comp g) (f'.comp f) n := by
  apply tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply, linearMap_tprod, NonUnitalAlgHom.comp_apply]

/-- The native lift of an actual linear map; its carrier function is `up ∘ f ∘ down`. -/
def liftLinearMap (f : M →ₗ[k] N) :
    ULift.{z} M →ₗ[k] ULift.{z} N :=
  (ULift.moduleEquiv : ULift.{z} N ≃ₗ[k] N).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M).toLinearMap)

@[simp]
theorem liftLinearMap_up (f : M →ₗ[k] N) (m : M) :
    liftLinearMap f (ULift.up m) = ULift.up (f m) := rfl

end TensorMaps

section FaceCompatibility

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  {N : Type w'} [AddCommGroup N] [Module k N]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The degree maps commute with every face when they respect the two actions. -/
theorem linearMap_face_comm (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) (i : Fin (n + 2)) :
    (face k B N n i).hom.comp (linearMap g f (n + 1)) =
      (linearMap g f n).comp (face k A M n i).hom := by
  apply tensorPower_ext
  intro m a
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · simp only [LinearMap.comp_apply]
    rw [linearMap_tprod g f (n + 1) m a,
      face_first_tprod k B N n (f m) (fun j => g (a j)),
      face_first_tprod k A M n m a, linearMap_tprod]
    rw [hright]
    rfl
  · simp only [LinearMap.comp_apply, Fin.succ_last]
    rw [linearMap_tprod g f (n + 1) m a,
      face_last_tprod k B N n (f m) (fun j => g (a j)),
      face_last_tprod k A M n m a, linearMap_tprod]
    rw [hleft]
    rfl
  · simp only [LinearMap.comp_apply]
    rw [linearMap_tprod g f (n + 1) m a,
      face_inner_tprod k B N n l (f m) (fun j => g (a j)),
      face_inner_tprod k A M n l m a, linearMap_tprod]
    apply congrArg (fun q : TensorPower k n B => f m ⊗ₜ[k] q)
    apply congrArg (PiTensorProduct.tprod k)
    funext j
    simp only [hochschildMulAdjacent]
    split_ifs <;> simp only [map_mul]

/-- The signed boundaries commute; this proof needs no unit-preservation law. -/
theorem linearMap_boundary_comm (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    (boundary k B N n).hom.comp (linearMap g f (n + 1)) =
      (linearMap g f n).comp (boundary k A M n).hom := by
  apply LinearMap.ext
  intro z
  rw [boundary_eq_sum, boundary_eq_sum]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun t => (-1 : ℤ) ^ i.val • t)
    (LinearMap.congr_fun (linearMap_face_comm g f hleft hright n i) z)

/-- Genuine chain map in a native common universe, obtained by lifting the two raw carriers. -/
def liftedMap (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    chainComplex k A (ULift.{max u v v' w w'} M) ⟶
      chainComplex k B (ULift.{max u v v' w w'} N) :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (linearMap g (liftLinearMap f) n)) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      apply linearMap_boundary_comm g (liftLinearMap f)
      · intro a m
        change ULift.up (f (a • m.down)) = ULift.up (g a • f m.down)
        exact congrArg ULift.up (hleft a m.down)
      · intro a m
        change ULift.up (f (MulOpposite.op a • m.down)) =
          ULift.up (MulOpposite.op (g a) • f m.down)
        exact congrArg ULift.up (hright a m.down))

/-- The common-universe map retains the exact raw coefficient/algebra generator formula. -/
theorem liftedMap_f_tprod (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) (m : M) (a : Fin n → A) :
    ((liftedMap g f hleft hright).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        ULift.up (f m) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) := by
  change linearMap g (liftLinearMap f) n
    (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [linearMap_tprod, liftLinearMap_up]

/-- The same literal tensor chain map at a specified canonical common lift
height. The maximum includes every source and target universe. -/
def liftedMapAt.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} M) ⟶
      chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N) :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (linearMap g (liftLinearMap f) n)) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      apply linearMap_boundary_comm g (liftLinearMap f)
      · intro a m
        change ULift.up (f (a • m.down)) = ULift.up (g a • f m.down)
        exact congrArg ULift.up (hleft a m.down)
      · intro a m
        change ULift.up (f (MulOpposite.op a • m.down)) =
          ULift.up (MulOpposite.op (g a) • f m.down)
        exact congrArg ULift.up (hright a m.down))

theorem liftedMapAt_f_tprod (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) (m : ULift.{max u v v' w w' z} M) (a : Fin n → A) :
    ((liftedMapAt.{z} g f hleft hright).f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (f m.down) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) := by
  change linearMap g
      (show ULift.{max u v v' w w' z} M →ₗ[k] ULift.{max u v v' w w' z} N from
        liftLinearMap f) n (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [linearMap_tprod]
  rfl

/-- The zero additional lift height gives the existing public chain map. -/
@[simp]
theorem liftedMapAt_zero (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    liftedMapAt.{0} g f hleft hright = liftedMap g f hleft hright := rfl

end FaceCompatibility


section LiftedMapAtLaws

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]
  {P : Type w''} [AddCommGroup P] [Module k P]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
  [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
  [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
  [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]

/-- Identity maps give the identity chain map at every canonical lift height. -/
@[simp]
theorem liftedMapAt_id.{z₁, u₁, v₁, w₁}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    :
    liftedMapAt.{z₁} (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
        (fun _ _ => rfl) (fun _ _ => rfl) =
      𝟙 (chainComplex k A (ULift.{max u₁ v₁ w₁ z₁} M)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  change linearMap (NonUnitalAlgHom.id k A)
      (show ULift.{max u₁ v₁ w₁ z₁} M →ₗ[k] ULift.{max u₁ v₁ w₁ z₁} M from
        liftLinearMap (LinearMap.id : M →ₗ[k] M)) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
    m ⊗ₜ[k] PiTensorProduct.tprod k a
  rw [linearMap_tprod]
  rfl

/-- Actual coefficient/algebra maps compose in the native common category at
one upper height containing all independent source/intermediate/target universes. -/
theorem liftedMapAt_comp.{z₁, u₁, v₁, v₂, v₃, w₁, w₂, w₃}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {C : Type v₃} [Ring C] [Algebra k C]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    {P : Type w₃} [AddCommGroup P] [Module k P]
    [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
    [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
    [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]
    (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (hleft' : ∀ b n, f' (b • n) = h b • f' n)
    (hright' : ∀ b n, f' (MulOpposite.op b • n) = MulOpposite.op (h b) • f' n) :
    liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} g f hleft hright ≫
        liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} h f' hleft' hright' =
      liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} (h.comp g) (f'.comp f)
        (fun a m => (congrArg f' (hleft a m)).trans (hleft' (g a) (f m)))
        (fun a m => (congrArg f' (hright a m)).trans (hright' (g a) (f m))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  change linearMap h
      (show ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} N →ₗ[k]
          ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P from liftLinearMap f') n
      (linearMap g
        (show ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M →ₗ[k]
            ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} N from liftLinearMap f) n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    linearMap (h.comp g)
      (show ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M →ₗ[k]
          ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P from liftLinearMap (f'.comp f)) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [linearMap_tprod, linearMap_tprod, linearMap_tprod]
  rfl

end LiftedMapAtLaws

section IndependentAlgebraCommonCarrierMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {M N : Type (max u v v' w)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The original tensor map for independently sized algebras and coefficients
already in a common category. No coefficient lift or bar comparison is needed. -/
def map (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    chainComplex k A M ⟶ chainComplex k B N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (linearMap g f n)) (by
    intro n
    rw [chainComplex_d, chainComplex_d]
    exact ModuleCat.hom_ext (linearMap_boundary_comm g f hleft hright n))

/-- Each degree uses the existing coefficient-first tensor linear map. -/
@[simp]
theorem map_f (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) (n : ℕ) :
    ((map g f hleft hright).f n).hom = linearMap g f n := rfl

theorem map_f_tprod (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) (m : M) (a : Fin n → A) :
    ((map g f hleft hright).f n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) :=
  linearMap_tprod g f n m a

end IndependentAlgebraCommonCarrierMaps

section
variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {M : Type (max u v w)} [AddCommGroup M]
  [Module k M]
  [Module A M]
  [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Native tensor identities give the original chain identity, with independent ambient worlds. -/
@[simp]
theorem map_id :
    map.{u, v, v, w}
      (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
      (fun _ _ => rfl) (fun _ _ => rfl) = 𝟙 (chainComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact linearMap_id n

end

section
variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C]
  {M N P : Type (max u v v' v'' w)} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module A M]
  [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N]
  [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
  [Module C P]
  [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
  [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
  [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]

/-- The existing independent-universe tensor-map composition is the chain composition. -/
theorem map_comp (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hl : ∀ a m, f (a • m) = g a • f m)
    (hr : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (hl' : ∀ b n, f' (b • n) = h b • f' n)
    (hr' : ∀ b n, f' (MulOpposite.op b • n) = MulOpposite.op (h b) • f' n) :
    map.{u, v, v', max u v v' v'' w} g f hl hr ≫
      map.{u, v', v'', max u v v' v'' w} h f' hl' hr' =
    map.{u, v, v'', max u v v' v'' w} (h.comp g) (f'.comp f)
      (fun a m => (congrArg f' (hl a m)).trans (hl' (g a) (f m)))
      (fun a m => (congrArg f' (hr a m)).trans (hr' (g a) (f m))) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact linearMap_comp g h f f' n

end


section CoefficientLiftLevels

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]

/-- Unlift only the coefficient in the literal Hochschild tensor level. -/
def coefficientUnliftEquiv (n : ℕ) :
    ULift.{z} M ⊗[k] TensorPower k n A ≃ₗ[k] M ⊗[k] TensorPower k n A :=
  TensorProduct.congr (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M)
    (LinearEquiv.refl k (TensorPower k n A))

@[simp]
theorem coefficientUnliftEquiv_tprod (n : ℕ) (m : ULift.{z} M) (a : Fin n → A) :
    coefficientUnliftEquiv k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m.down ⊗ₜ[k] PiTensorProduct.tprod k a := by
  change TensorProduct.congr (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-- The native tensor map for coefficient down is the unlift equivalence. -/
theorem linearMap_coefficientUnlift (n : ℕ) :
    linearMap (NonUnitalAlgHom.id k A)
        (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M).toLinearMap n =
      (coefficientUnliftEquiv k A M n).toLinearMap := by
  apply tensorPower_ext
  intro m a
  rw [linearMap_tprod]
  change m.down ⊗ₜ[k] PiTensorProduct.tprod k a =
    coefficientUnliftEquiv k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  exact (coefficientUnliftEquiv_tprod k A M n m a).symm

/-- Lift the whole tensor after unlifting its coefficient; this is the native
whole-level carrier of `ModuleCat.uliftFunctor`. -/
def coefficientLiftEquiv (n : ℕ) :
    ULift.{z} M ⊗[k] TensorPower k n A ≃ₗ[k] ULift.{z} (M ⊗[k] TensorPower k n A) :=
  (coefficientUnliftEquiv k A M n).trans
    (ULift.moduleEquiv : ULift.{z} (M ⊗[k] TensorPower k n A) ≃ₗ[k]
      M ⊗[k] TensorPower k n A).symm

@[simp]
theorem coefficientLiftEquiv_tprod (n : ℕ) (m : ULift.{z} M) (a : Fin n → A) :
    coefficientLiftEquiv k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (m.down ⊗ₜ[k] PiTensorProduct.tprod k a) := by
  simp only [coefficientLiftEquiv, LinearEquiv.trans_apply, coefficientUnliftEquiv_tprod]
  rfl

@[simp]
theorem coefficientLiftEquiv_symm_up_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    (coefficientLiftEquiv k A M n).symm
        (ULift.up (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a := by
  apply (coefficientLiftEquiv k A M n).injective
  rw [LinearEquiv.apply_symm_apply, coefficientLiftEquiv_tprod]

end CoefficientLiftLevels

section CoefficientLiftComplex

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Coefficient down commutes with every actual face, including both actions. -/
theorem coefficientUnliftEquiv_face_comm (n : ℕ) (i : Fin (n + 2)) :
    (face k A M n i).hom.comp (coefficientUnliftEquiv k A M (n + 1)).toLinearMap =
      (coefficientUnliftEquiv k A M n).toLinearMap.comp
        (face k A (ULift.{z} M) n i).hom := by
  have h := linearMap_face_comm (NonUnitalAlgHom.id k A)
    (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M).toLinearMap
    (fun _ _ => rfl) (fun _ _ => rfl) n i
  rw [linearMap_coefficientUnlift, linearMap_coefficientUnlift] at h
  exact h

/-- The lifted first face keeps the right coefficient action, in every degree. -/
theorem coefficientLift_first_face_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    coefficientLiftEquiv k A M n
        ((face k A (ULift.{z} M) n 0).hom
          (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up ((MulOpposite.op (a 0) • m) ⊗ₜ[k]
        PiTensorProduct.tprod k (hochschildDropFirst a)) := by
  rw [face_first_tprod, coefficientLiftEquiv_tprod]
  rfl

/-- The lifted last face keeps the left coefficient action, in every degree. -/
theorem coefficientLift_last_face_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    coefficientLiftEquiv k A M n
        ((face k A (ULift.{z} M) n (Fin.last (n + 1))).hom
          (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up ((a (Fin.last n) • m) ⊗ₜ[k]
        PiTensorProduct.tprod k (hochschildDropLast a)) := by
  rw [face_last_tprod, coefficientLiftEquiv_tprod]
  rfl

/-- The signed Hochschild boundary commutes with coefficient down. -/
theorem coefficientUnliftEquiv_boundary_comm (n : ℕ) :
    (boundary k A M n).hom.comp (coefficientUnliftEquiv k A M (n + 1)).toLinearMap =
      (coefficientUnliftEquiv k A M n).toLinearMap.comp
        (boundary k A (ULift.{z} M) n).hom := by
  have h := linearMap_boundary_comm (NonUnitalAlgHom.id k A)
    (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M).toLinearMap
    (fun _ _ => rfl) (fun _ _ => rfl) n
  rw [linearMap_coefficientUnlift, linearMap_coefficientUnlift] at h
  exact h

/-- The literal degree equivalence intertwines the native whole-level ULift
map with the coefficient-lift boundary. -/
theorem coefficientLiftEquiv_boundary_comm (n : ℕ) :
    (show ULift.{z} (M ⊗[k] TensorPower k (n + 1) A) →ₗ[k]
        ULift.{z} (M ⊗[k] TensorPower k n A) from
      liftLinearMap (boundary k A M n).hom).comp
        (coefficientLiftEquiv k A M (n + 1)).toLinearMap =
      (coefficientLiftEquiv k A M n).toLinearMap.comp
        (boundary k A (ULift.{z} M) n).hom := by
  apply LinearMap.ext
  intro x
  apply (ULift.moduleEquiv : ULift.{z} (M ⊗[k] TensorPower k n A) ≃ₗ[k]
    M ⊗[k] TensorPower k n A).injective
  change (boundary k A M n).hom ((coefficientUnliftEquiv k A M (n + 1)) x) =
    (coefficientUnliftEquiv k A M n) ((boundary k A (ULift.{z} M) n).hom x)
  exact LinearMap.congr_fun (coefficientUnliftEquiv_boundary_comm k A M n) x

/-- The coefficient-lift complex is the native whole-complex ULift.
No comparison module, homotopy, or isomorphism is an input. -/
def coefficientLiftComplexIso :
    chainComplex k A (ULift.{z} M) ≅
      ((ModuleCat.uliftFunctor.{z, max u v w} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (chainComplex k A M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientLiftEquiv k A M n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      rw [Functor.mapHomologicalComplex_obj_d, chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp]
      change (show ULift.{z} (M ⊗[k] TensorPower k (j + 1) A) →ₗ[k]
          ULift.{z} (M ⊗[k] TensorPower k j A) from
        liftLinearMap (boundary k A M j).hom).comp
          (coefficientLiftEquiv k A M (j + 1)).toLinearMap =
        (coefficientLiftEquiv k A M j).toLinearMap.comp
          (boundary k A (ULift.{z} M) j).hom
      exact coefficientLiftEquiv_boundary_comm k A M j)

@[simp]
theorem coefficientLiftComplexIso_hom_f (n : ℕ) :
    ((coefficientLiftComplexIso k A M).hom.f n).hom =
      (coefficientLiftEquiv k A M n).toLinearMap := rfl

/-- The inverse degree component of the whole-complex lift comparison. -/
@[simp]
theorem coefficientLiftComplexIso_inv_f (n : ℕ) :
    ((coefficientLiftComplexIso k A M).inv.f n).hom =
      (coefficientLiftEquiv k A M n).symm.toLinearMap := rfl

/-- The raw HH coefficient-lift comparison, obtained from the chain
iso and native homology preservation by the exact ULift functor. -/
def coefficientLiftHomologyIso (n : ℕ) :
    homology k A (ULift.{z} M) n ≅
      (ModuleCat.uliftFunctor.{z, max u v w} k).obj (homology k A M n) := by
  let F : ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w z} k :=
    ModuleCat.uliftFunctor.{z, max u v w} k
  let K : ChainComplex (ModuleCat.{max u v w} k) ℕ := chainComplex k A M
  let L : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  have e : chainComplex k A (ULift.{z} M) ≅ L := coefficientLiftComplexIso k A M
  refine (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w z} k)
    (ComplexShape.down ℕ) n).mapIso e ≪≫ ?_
  exact (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app K

/-- Characteristic factorization of the HH lift comparison into the
actual chain comparison and the native exact-functor homology comparison. -/
theorem coefficientLiftHomologyIso_hom_eq (n : ℕ) :
    (coefficientLiftHomologyIso k A M n).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w z} k)
        (ComplexShape.down ℕ) n).map (coefficientLiftComplexIso k A M).hom ≫
      (((chainComplex k A M).sc n).mapHomologyIso
        (ModuleCat.uliftFunctor.{z, max u v w} k)).hom := rfl

/-- The lift comparison on the original module carriers, obtained by
following its native homology isomorphism with coefficient down. -/
def coefficientLiftRawHomologyEquiv.{z₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    (n : ℕ) :
    (homology k A (ULift.{z₁} M) n).carrier ≃ₗ[k] (homology k A M n).carrier := by
  let γ : homology k A (ULift.{z₁} M) n ≅
      (ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k).obj (homology k A M n) :=
    coefficientLiftHomologyIso k A M n
  exact γ.toLinearEquiv.trans
    (ULift.moduleEquiv : ULift.{z₁} (homology k A M n).carrier ≃ₗ[k]
      (homology k A M n).carrier)

end CoefficientLiftComplex


section SameUniverseMaps

variable {k : Type u} [CommRing k]
  {A B C : Type v} [Ring A] [Ring B] [Ring C] [Algebra k A] [Algebra k B] [Algebra k C]
  {M N P : Type w} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
  [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
  [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
  [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]

/-- Compatibility with the original low coefficient world. The raw map is
obtained by descending the canonical map through the fully faithful native
universe-lift functor; its source and target are the original complexes. -/
def mapInSameUniverse (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    chainComplex k A M ⟶ chainComplex k B N :=
  let U := (ModuleCat.uliftFunctor.{max u v w, max u v w} k).mapHomologicalComplex
    (ComplexShape.down ℕ)
  U.preimage ((coefficientLiftComplexIso.{u, v, w, max u v w} k A M).inv ≫
    map g (show ULift.{max u v w} M →ₗ[k] ULift.{max u v w} N from liftLinearMap f)
      (fun a m => congrArg ULift.up (hleft a m.down))
      (fun a m => congrArg ULift.up (hright a m.down)) ≫
    (coefficientLiftComplexIso.{u, v, w, max u v w} k B N).hom)

/-- Descending the canonical map keeps the original coefficient-first formula. -/
@[simp]
theorem mapInSameUniverse_f (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) (n : ℕ) :
    ((mapInSameUniverse g f hleft hright).f n).hom = linearMap g f n := by
  let U := (ModuleCat.uliftFunctor.{max u v w, max u v w} k).mapHomologicalComplex
    (ComplexShape.down ℕ)
  have h := U.map_preimage ((coefficientLiftComplexIso.{u, v, w, max u v w} k A M).inv ≫
    map g (show ULift.{max u v w} M →ₗ[k] ULift.{max u v w} N from liftLinearMap f)
      (fun a m => congrArg ULift.up (hleft a m.down))
      (fun a m => congrArg ULift.up (hright a m.down)) ≫
    (coefficientLiftComplexIso.{u, v, w, max u v w} k B N).hom)
  apply tensorPower_ext
  intro m a
  have hn := congrArg (fun q => (q.f n).hom) h
  have hx := LinearMap.congr_fun hn (ULift.up (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  change ULift.up (((mapInSameUniverse g f hleft hright).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    (coefficientLiftEquiv k B N n)
      (linearMap g (show ULift.{max u v w} M →ₗ[k] ULift.{max u v w} N from
        liftLinearMap f) n ((coefficientLiftEquiv k A M n).symm
          (ULift.up (m ⊗ₜ[k] PiTensorProduct.tprod k a)))) at hx
  rw [coefficientLiftEquiv_symm_up_tprod, linearMap_tprod,
    coefficientLiftEquiv_tprod] at hx
  exact (ULift.up_injective hx).trans (linearMap_tprod g f n m a).symm

/-- The induced homology morphism retains the original coefficient world. -/
def homologyMap (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) (n : ℕ) :
    homology k A M n ⟶ homology k B N n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) n).map
    (mapInSameUniverse g f hleft hright)

end SameUniverseMaps

section CoefficientLiftComposition

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Flatten the coefficient in the literal tensor degree; the algebra factors
and both their coefficient actions retain their actual noncommutative order. -/
def coefficientFlattenEquiv.{z₁, t₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    (n : ℕ) :
    ULift.{t₁} (ULift.{z₁} M) ⊗[k] TensorPower k n A ≃ₗ[k]
      ULift.{max z₁ t₁} M ⊗[k] TensorPower k n A :=
  TensorProduct.congr (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M)
    (LinearEquiv.refl k (TensorPower k n A))

omit [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] in
@[simp]
theorem coefficientFlattenEquiv_tprod (n : ℕ)
    (m : ULift.{t} (ULift.{z} M)) (a : Fin n → A) :
    coefficientFlattenEquiv k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up m.down.down ⊗ₜ[k] PiTensorProduct.tprod k a := by
  rw [coefficientFlattenEquiv, TensorProduct.congr_tmul]
  rfl

/-- The coefficient-flattening chain isomorphism. -/
def coefficientFlattenComplexIso.{z₁, t₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    :
    chainComplex k A (ULift.{t₁} (ULift.{z₁} M)) ≅
      chainComplex k A (ULift.{max z₁ t₁} M) where
  hom := mapInSameUniverse (NonUnitalAlgHom.id k A)
    (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).toLinearMap
    (fun _ _ => rfl) (fun _ _ => rfl)
  inv := mapInSameUniverse (NonUnitalAlgHom.id k A)
    (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).symm.toLinearMap
    (fun _ _ => rfl) (fun _ _ => rfl)
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_id, mapInSameUniverse_f]
    erw [mapInSameUniverse_f, mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A)
        (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).symm.toLinearMap n
        (linearMap (NonUnitalAlgHom.id k A)
          (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).toLinearMap n
          (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = m ⊗ₜ[k] PiTensorProduct.tprod k a
    rw [linearMap_tprod, linearMap_tprod]
    change (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).symm
        ((ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M) m) ⊗ₜ[k]
        PiTensorProduct.tprod k a = m ⊗ₜ[k] PiTensorProduct.tprod k a
    rw [LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_id, mapInSameUniverse_f]
    erw [mapInSameUniverse_f, mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A)
        (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).toLinearMap n
        (linearMap (NonUnitalAlgHom.id k A)
          (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).symm.toLinearMap n
          (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = m ⊗ₜ[k] PiTensorProduct.tprod k a
    rw [linearMap_tprod, linearMap_tprod]
    change (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M)
        ((ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).symm m) ⊗ₜ[k]
        PiTensorProduct.tprod k a = m ⊗ₜ[k] PiTensorProduct.tprod k a
    rw [LinearEquiv.apply_symm_apply]

theorem coefficientFlattenComplexIso_hom_f_tprod (n : ℕ)
    (m : ULift.{t} (ULift.{z} M)) (a : Fin n → A) :
    ((coefficientFlattenComplexIso k A M).hom.f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up m.down.down ⊗ₜ[k] PiTensorProduct.tprod k a := by
  simp only [coefficientFlattenComplexIso, mapInSameUniverse_f]
  erw [mapInSameUniverse_f]
  change linearMap (NonUnitalAlgHom.id k A)
      (ModuleCat.uliftFlattenEquiv.{z, t} k M).toLinearMap n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [linearMap_tprod]
  rfl

/-- The whole-complex lift comparisons commute with the coefficient
and whole-module flattening maps. All intermediate native endpoints are fixed. -/
theorem coefficientLiftComplexIso_comp.{z₁, t₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    :
    let F : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁} k :=
      ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k
    let G : ModuleCat.{max u₁ v₁ w₁ z₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
      ModuleCat.uliftFunctor.{t₁, max u₁ v₁ w₁ z₁} k
    let F' : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
      ModuleCat.uliftFunctor.{max z₁ t₁, max u₁ v₁ w₁} k
    let eZ : chainComplex k A (ULift.{z₁} M) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (chainComplex k A M) :=
      coefficientLiftComplexIso k A M
    let eT : chainComplex k A (ULift.{t₁} (ULift.{z₁} M)) ≅
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k A (ULift.{z₁} M)) := coefficientLiftComplexIso k A (ULift.{z₁} M)
    let eZT : chainComplex k A (ULift.{max z₁ t₁} M) ≅
        (F'.mapHomologicalComplex (ComplexShape.down ℕ)).obj (chainComplex k A M) :=
      coefficientLiftComplexIso k A M
    eT.hom ≫ (G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom ≫
        (Functor.mapHomologicalComplexCompIso
          (ModuleCat.uliftFunctorCompIso.{z₁, t₁, max u₁ v₁ w₁} k)
          (ComplexShape.down ℕ)).hom.app (chainComplex k A M) =
      (coefficientFlattenComplexIso.{z₁, t₁} k A M).hom ≫ eZT.hom := by
  dsimp only
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  simp only [coefficientFlattenComplexIso, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, ModuleCat.hom_comp, ModuleCat.hom_id,
    Functor.mapHomologicalComplex_map_f, ModuleCat.uliftFunctor_map,
    mapInSameUniverse_f]
  erw [mapInSameUniverse_f]
  apply tensorPower_ext
  intro m a
  change
    (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k (M ⊗[k] TensorPower k n A))
        (ULift.up (coefficientLiftEquiv k A M n
          ((coefficientLiftEquiv k A (ULift.{z₁} M) n)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a)).down)) =
      coefficientLiftEquiv k A M n
        (linearMap (NonUnitalAlgHom.id k A)
          (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M).toLinearMap n
          (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  rw [coefficientLiftEquiv_tprod, linearMap_tprod]
  change
    (ModuleCat.uliftFlattenEquiv.{z₁, t₁} k (M ⊗[k] TensorPower k n A))
        (ULift.up (coefficientLiftEquiv k A M n
          (m.down ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      coefficientLiftEquiv k A M n
        ((ModuleCat.uliftFlattenEquiv.{z₁, t₁} k M) m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [coefficientLiftEquiv_tprod, coefficientLiftEquiv_tprod]
  rfl

/-- The HH homology comparisons commute with native lift composition
and the coefficient-flattening chain map. -/
theorem coefficientLiftHomologyIso_comp.{z₁, t₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    (n : ℕ) :
    let F : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁} k :=
      ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k
    let G : ModuleCat.{max u₁ v₁ w₁ z₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
      ModuleCat.uliftFunctor.{t₁, max u₁ v₁ w₁ z₁} k
    let F' : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
      ModuleCat.uliftFunctor.{max z₁ t₁, max u₁ v₁ w₁} k
    let γZ : homology k A (ULift.{z₁} M) n ≅ F.obj (homology k A M n) :=
      coefficientLiftHomologyIso k A M n
    let γT : homology k A (ULift.{t₁} (ULift.{z₁} M)) n ≅
        G.obj (homology k A (ULift.{z₁} M) n) :=
      coefficientLiftHomologyIso k A (ULift.{z₁} M) n
    let γZT : homology k A (ULift.{max z₁ t₁} M) n ≅ F'.obj (homology k A M n) :=
      coefficientLiftHomologyIso k A M n
    HomologicalComplex.homologyMap (coefficientFlattenComplexIso.{z₁, t₁} k A M).hom n ≫
        γZT.hom =
      γT.hom ≫ G.map γZ.hom ≫
        (ModuleCat.uliftFunctorCompIso.{z₁, t₁, max u₁ v₁ w₁} k).hom.app (homology k A M n) := by
  dsimp only
  let F : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁} k :=
    ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k
  let G : ModuleCat.{max u₁ v₁ w₁ z₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
    ModuleCat.uliftFunctor.{t₁, max u₁ v₁ w₁ z₁} k
  let F' : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k :=
    ModuleCat.uliftFunctor.{max z₁ t₁, max u₁ v₁ w₁} k
  let K : ChainComplex (ModuleCat.{max u₁ v₁ w₁} k) ℕ := chainComplex k A M
  let KZ : ChainComplex (ModuleCat.{max u₁ v₁ w₁ z₁} k) ℕ :=
    chainComplex k A (ULift.{z₁} M)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ w₁ z₁ t₁} k)
    (ComplexShape.down ℕ) n
  let HZ := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ w₁ z₁} k)
    (ComplexShape.down ℕ) n
  let eZ : KZ ≅ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    coefficientLiftComplexIso k A M
  let eT : chainComplex k A (ULift.{t₁} (ULift.{z₁} M)) ≅
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj KZ :=
    coefficientLiftComplexIso k A (ULift.{z₁} M)
  let eZT : chainComplex k A (ULift.{max z₁ t₁} M) ≅
      (F'.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    coefficientLiftComplexIso k A M
  let q := coefficientFlattenComplexIso.{z₁, t₁} k A M
  let δ : F ⋙ G ≅ F' := ModuleCat.uliftFunctorCompIso.{z₁, t₁, max u₁ v₁ w₁} k
  let δC := Functor.mapHomologicalComplexCompIso δ (ComplexShape.down ℕ)
  let cZ : HZ.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      F.obj (K.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app K
  let cT : H.obj ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj KZ) ≅
      G.obj (HZ.obj KZ) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n G).app KZ
  let cTZ : H.obj ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) ≅
      G.obj (HZ.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n G).app
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
  let cZT : H.obj ((F'.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      F'.obj (K.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F').app K
  let cFG : H.obj ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) ≅
      (F ⋙ G).obj (K.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n (F ⋙ G)).app K
  let γZ : homology k A (ULift.{z₁} M) n ≅ F.obj (homology k A M n) :=
    coefficientLiftHomologyIso k A M n
  let γT : homology k A (ULift.{t₁} (ULift.{z₁} M)) n ≅ G.obj (homology k A (ULift.{z₁} M) n) :=
    coefficientLiftHomologyIso k A (ULift.{z₁} M) n
  let γZT : homology k A (ULift.{max z₁ t₁} M) n ≅ F'.obj (homology k A M n) :=
    coefficientLiftHomologyIso k A M n
  have hz : γZ.hom = HZ.map eZ.hom ≫ cZ.hom :=
    coefficientLiftHomologyIso_hom_eq k A M n
  have ht : γT.hom = H.map eT.hom ≫ cT.hom :=
    coefficientLiftHomologyIso_hom_eq k A (ULift.{z₁} M) n
  have hzt : γZT.hom = H.map eZT.hom ≫ cZT.hom :=
    coefficientLiftHomologyIso_hom_eq k A M n
  have hGnat : H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫
      cTZ.hom = cT.hom ≫ G.map (HZ.map eZ.hom) := by
    have h := (HomologicalComplex.mapHomologyFunctorIso
      (c := ComplexShape.down ℕ) n G).hom.naturality eZ.hom
    change H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫
      cTZ.hom = cT.hom ≫ G.map (HZ.map eZ.hom) at h
    exact h
  have hcomp : cFG.hom = cTZ.hom ≫ G.map cZ.hom := by
    change ((K.sc n).mapHomologyIso (F ⋙ G)).hom =
      (((K.sc n).map F).mapHomologyIso G).hom ≫ G.map ((K.sc n).mapHomologyIso F).hom
    exact ShortComplex.mapHomologyIso_comp_hom (K.sc n) F G
  have hδ : cFG.hom ≫ δ.hom.app (K.homology n) =
      H.map (δC.hom.app K) ≫ cZT.hom := by
    dsimp only [H]
    rw [HomologicalComplex.homologyFunctor_map]
    change cFG.hom ≫ δ.hom.app (K.sc n).homology =
      ShortComplex.homologyMap ((K.sc n).mapNatTrans δ.hom) ≫ cZT.hom
    exact NatTrans.mapHomologyIso_hom_comp_app_homology δ.hom (K.sc n)
  have hchain : eT.hom ≫ (G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom ≫
      δC.hom.app K = q.hom ≫ eZT.hom :=
    coefficientLiftComplexIso_comp.{z₁, t₁} k A M
  have hchainH : H.map eT.hom ≫
      H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫
      H.map (δC.hom.app K) = H.map q.hom ≫ H.map eZT.hom := by
    simpa only [Functor.map_comp] using
      congrArg (fun f : chainComplex k A (ULift.{t₁} (ULift.{z₁} M)) ⟶
        (F'.mapHomologicalComplex (ComplexShape.down ℕ)).obj K => H.map f) hchain
  change H.map q.hom ≫ γZT.hom = γT.hom ≫ G.map γZ.hom ≫ δ.hom.app (K.homology n)
  rw [hz, ht, hzt]
  symm
  have h₀ :
      ((H.map eT.hom ≫ cT.hom) ≫ G.map (HZ.map eZ.hom ≫ cZ.hom) ≫
        δ.hom.app (K.homology n)) =
      (H.map eT.hom ≫ ((cT.hom ≫ G.map (HZ.map eZ.hom)) ≫ G.map cZ.hom) ≫
        δ.hom.app (K.homology n)) := by simp only [Functor.map_comp, Category.assoc]
  have h₁ :
      (H.map eT.hom ≫ ((cT.hom ≫ G.map (HZ.map eZ.hom)) ≫ G.map cZ.hom) ≫
        δ.hom.app (K.homology n)) =
      (H.map eT.hom ≫
        ((H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫ cTZ.hom) ≫
          G.map cZ.hom) ≫ δ.hom.app (K.homology n)) := by rw [← hGnat]
  have h₂ :
      (H.map eT.hom ≫
        ((H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫ cTZ.hom) ≫
          G.map cZ.hom) ≫ δ.hom.app (K.homology n)) =
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        (cTZ.hom ≫ G.map cZ.hom) ≫ δ.hom.app (K.homology n)) := by
      simp only [Category.assoc]
  have h₃ :
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        (cTZ.hom ≫ G.map cZ.hom) ≫ δ.hom.app (K.homology n)) =
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        cFG.hom ≫ δ.hom.app (K.homology n)) := by rw [← hcomp]
  have h₄ :
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        cFG.hom ≫ δ.hom.app (K.homology n)) =
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        (H.map (δC.hom.app K) ≫ cZT.hom)) := by
    simpa only [Category.assoc] using
      congrArg (fun f => (H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫ f) hδ
  have h₅ :
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom)) ≫
        (H.map (δC.hom.app K) ≫ cZT.hom)) =
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫
        H.map (δC.hom.app K)) ≫ cZT.hom) := by simp only [Category.assoc]
  have h₆ :
      ((H.map eT.hom ≫
        H.map ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map eZ.hom) ≫
        H.map (δC.hom.app K)) ≫ cZT.hom) =
      ((H.map q.hom ≫ H.map eZT.hom) ≫ cZT.hom) :=
    congrArg (fun f => f ≫ cZT.hom) hchainH
  have h₇ :
      ((H.map q.hom ≫ H.map eZT.hom) ≫ cZT.hom) =
      (H.map q.hom ≫ (H.map eZT.hom ≫ cZT.hom)) := Category.assoc _ _ _
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇)))))))

/-- Returning the homology carrier after coefficient flattening agrees with
returning it through the two actual lift comparisons. -/
theorem coefficientLiftRawHomologyEquiv_comp.{z₁, t₁, u₁, v₁, w₁}
    (k : Type u₁) [CommRing k]
    (A : Type v₁) [Ring A] [Algebra k A]
    (M : Type w₁) [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    (n : ℕ) :
    (coefficientLiftRawHomologyEquiv.{max z₁ t₁} k A M n).toLinearMap.comp
        (HomologicalComplex.homologyMap
          (coefficientFlattenComplexIso.{z₁, t₁} k A M).hom n).hom =
      (coefficientLiftRawHomologyEquiv.{z₁} k A M n).toLinearMap.comp
        (coefficientLiftRawHomologyEquiv.{t₁} k A (ULift.{z₁} M) n).toLinearMap := by
  have hc := coefficientLiftHomologyIso_comp.{z₁, t₁} k A M n
  dsimp only at hc
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun f : homology k A (ULift.{t₁} (ULift.{z₁} M)) n ⟶
        (ModuleCat.uliftFunctor.{max z₁ t₁, max u₁ v₁ w₁} k).obj (homology k A M n) =>
      f.hom x) hc
  exact congrArg ULift.down hx

end CoefficientLiftComposition

section CoefficientLiftNaturality

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- The coefficient/whole-level lift comparison is natural for the heterogeneous tensor maps, without requiring unit preservation. -/
theorem coefficientLiftEquiv_linearMap_comm (g : A →ₙₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    (coefficientLiftEquiv k B N n).toLinearMap.comp
        (linearMap g (show ULift.{z} M →ₗ[k] ULift.{z} N from liftLinearMap f) n) =
      (show ULift.{z} (M ⊗[k] TensorPower k n A) →ₗ[k]
          ULift.{z} (N ⊗[k] TensorPower k n B) from liftLinearMap (linearMap g f n)).comp
        (coefficientLiftEquiv k A M n).toLinearMap := by
  apply tensorPower_ext
  intro m a
  change coefficientLiftEquiv k B N n
      (linearMap g (liftLinearMap f) n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    liftLinearMap (linearMap g f n)
      (coefficientLiftEquiv k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  rw [linearMap_tprod g (liftLinearMap f) n m a,
    coefficientLiftEquiv_tprod k B N n (liftLinearMap f m) (fun j => g (a j)),
    coefficientLiftEquiv_tprod k A M n m a]
  change ULift.up (f m.down ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j))) =
    ULift.up (linearMap g f n (m.down ⊗ₜ[k] PiTensorProduct.tprod k a))
  exact congrArg ULift.up (linearMap_tprod g f n m.down a).symm

end CoefficientLiftNaturality

section CoefficientLiftChainNaturality

variable {k : Type u} [CommRing k]
  {A B : Type v} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The chain lift comparison is natural for coefficient/algebra maps
in the native common carrier category. Raw degree maps above allow independent
source/target universes. -/
@[reassoc]
theorem coefficientLiftComplexIso_naturality (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    mapInSameUniverse g (show ULift.{z} M →ₗ[k] ULift.{z} N from liftLinearMap f)
        (by
          intro a m
          change ULift.up (f (a • m.down)) = ULift.up (g a • f m.down)
          exact congrArg ULift.up (hleft a m.down))
        (by
          intro a m
          change ULift.up (f (MulOpposite.op a • m.down)) =
            ULift.up (MulOpposite.op (g a) • f m.down)
          exact congrArg ULift.up (hright a m.down)) ≫
      (coefficientLiftComplexIso k B N).hom =
    (coefficientLiftComplexIso k A M).hom ≫
      ((ModuleCat.uliftFunctor.{z, max u v w} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (mapInSameUniverse g f hleft hright) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  simp only [coefficientFlattenComplexIso, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, ModuleCat.hom_comp, ModuleCat.hom_id,
    Functor.mapHomologicalComplex_map_f, ModuleCat.uliftFunctor_map,
    mapInSameUniverse_f]
  change (coefficientLiftEquiv k B N n).toLinearMap.comp
      (linearMap g (show ULift.{z} M →ₗ[k] ULift.{z} N from liftLinearMap f) n) =
    (show ULift.{z} (M ⊗[k] TensorPower k n A) →ₗ[k]
        ULift.{z} (N ⊗[k] TensorPower k n B) from liftLinearMap (linearMap g f n)).comp
      (coefficientLiftEquiv k A M n).toLinearMap
  exact coefficientLiftEquiv_linearMap_comm g f n

/-- The native exact-functor homology comparison is natural for the coefficient and algebra chain maps. -/
@[reassoc]
theorem coefficientLiftHomologyIso_naturality.{z₁, u₁, v₁, w₁}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₁} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₁} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    homologyMap g (show ULift.{z₁} M →ₗ[k] ULift.{z₁} N from liftLinearMap f)
        (by
          intro a m
          change ULift.up (f (a • m.down)) = ULift.up (g a • f m.down)
          exact congrArg ULift.up (hleft a m.down))
        (by
          intro a m
          change ULift.up (f (MulOpposite.op a • m.down)) =
            ULift.up (MulOpposite.op (g a) • f m.down)
          exact congrArg ULift.up (hright a m.down)) n ≫
      (coefficientLiftHomologyIso k B N n).hom =
    (coefficientLiftHomologyIso k A M n).hom ≫
      (ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k).map
        (homologyMap g f hleft hright n) := by
  let F : ModuleCat.{max u₁ v₁ w₁} k ⥤ ModuleCat.{max u₁ v₁ w₁ z₁} k :=
    ModuleCat.uliftFunctor.{z₁, max u₁ v₁ w₁} k
  let K : ChainComplex (ModuleCat.{max u₁ v₁ w₁} k) ℕ := chainComplex k A M
  let L : ChainComplex (ModuleCat.{max u₁ v₁ w₁} k) ℕ := chainComplex k B N
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ w₁ z₁} k)
    (ComplexShape.down ℕ) n
  let ρ : K ⟶ L := mapInSameUniverse g f hleft hright
  let ψ : chainComplex k A (ULift.{z₁} M) ⟶ chainComplex k B (ULift.{z₁} N) :=
    mapInSameUniverse g (show ULift.{z₁} M →ₗ[k] ULift.{z₁} N from liftLinearMap f)
      (fun a m => congrArg ULift.up (hleft a m.down))
      (fun a m => congrArg ULift.up (hright a m.down))
  let eK := coefficientLiftComplexIso k A M
  let eL := coefficientLiftComplexIso k B N
  let cK : H.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      F.obj (K.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app K
  let cL : H.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) ≅
      F.obj (L.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app L
  have hchain : ψ ≫ eL.hom = eK.hom ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ :=
    coefficientLiftComplexIso_naturality g f hleft hright
  have hchainH : H.map ψ ≫ H.map eL.hom = H.map eK.hom ≫
      H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ) := by
    simpa only [Functor.map_comp] using
      congrArg (fun q : chainComplex k A (ULift.{z₁} M) ⟶
          (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L => H.map q) hchain
  have hpres : H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ) ≫
      cL.hom = cK.hom ≫ F.map (HomologicalComplex.homologyMap ρ n) := by
    have h := (HomologicalComplex.mapHomologyFunctorIso
      (c := ComplexShape.down ℕ) n F).hom.naturality ρ
    change H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ) ≫
      cL.hom = cK.hom ≫ F.map (HomologicalComplex.homologyMap ρ n) at h
    exact h
  change H.map ψ ≫ (coefficientLiftHomologyIso k B N n).hom =
    (coefficientLiftHomologyIso k A M n).hom ≫ F.map (HomologicalComplex.homologyMap ρ n)
  rw [coefficientLiftHomologyIso_hom_eq, coefficientLiftHomologyIso_hom_eq]
  change H.map ψ ≫ (H.map eL.hom ≫ cL.hom) =
    (H.map eK.hom ≫ cK.hom) ≫ F.map (HomologicalComplex.homologyMap ρ n)
  have h₁ : H.map ψ ≫ (H.map eL.hom ≫ cL.hom) =
      (H.map ψ ≫ H.map eL.hom) ≫ cL.hom := (Category.assoc _ _ _).symm
  have h₂ : (H.map ψ ≫ H.map eL.hom) ≫ cL.hom =
      (H.map eK.hom ≫
        H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ)) ≫ cL.hom :=
    congrArg (fun q => q ≫ cL.hom) hchainH
  have h₃ : (H.map eK.hom ≫
        H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ρ)) ≫ cL.hom =
      H.map eK.hom ≫ (cK.hom ≫ F.map (HomologicalComplex.homologyMap ρ n)) := by
    rw [Category.assoc, hpres]
  have h₄ : H.map eK.hom ≫ (cK.hom ≫ F.map (HomologicalComplex.homologyMap ρ n)) =
      (H.map eK.hom ≫ cK.hom) ≫ F.map (HomologicalComplex.homologyMap ρ n) :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end CoefficientLiftChainNaturality


section LiftedMapHeightComparison

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N] [Module Bᵐᵒᵖ N]
  [SMulCommClass B Bᵐᵒᵖ N] [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- Increasing the canonical common height gives the same actual tensor chain
map after coefficient flattening and the native whole-complex lift comparison. -/
theorem liftedMapAt_flatten.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    let F : ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k ⥤ ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k :=
      ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k
    let eM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) :=
      coefficientLiftComplexIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
    let eN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) :=
      coefficientLiftComplexIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
    let qM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
        chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} M) :=
      coefficientFlattenComplexIso.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k A M
    let qN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
        chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N) :=
      coefficientFlattenComplexIso.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k B N
    qM.hom ≫ liftedMapAt.{z₁} g f hleft hright =
      eM.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (liftedMap g f hleft hright) ≫ eN.inv ≫ qN.hom := by
  dsimp only
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  simp only [coefficientFlattenComplexIso, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, ModuleCat.hom_comp, ModuleCat.hom_id,
    Functor.mapHomologicalComplex_map_f, ModuleCat.uliftFunctor_map,
    mapInSameUniverse_f]
  erw [mapInSameUniverse_f]
  repeat' erw [ModuleCat.hom_comp]
  erw [mapInSameUniverse_f]
  apply tensorPower_ext
  intro m a
  change linearMap g
      (show ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} M →ₗ[k] ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N from
        liftLinearMap f) n
      (linearMap (NonUnitalAlgHom.id k A)
        (ModuleCat.uliftFlattenEquiv.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k M).toLinearMap n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    linearMap (NonUnitalAlgHom.id k B)
      (ModuleCat.uliftFlattenEquiv.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k N).toLinearMap n
      ((coefficientLiftEquiv k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n).symm
        (ULift.up (linearMap g
          (show ULift.{max u₁ v₁ v₂ w₁ w₂} M →ₗ[k] ULift.{max u₁ v₁ v₂ w₁ w₂} N from
            liftLinearMap f) n
          ((coefficientLiftEquiv k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a)).down)))
  rw [linearMap_tprod, linearMap_tprod, coefficientLiftEquiv_tprod, linearMap_tprod]
  change ULift.up (f m.down.down) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) =
    linearMap (NonUnitalAlgHom.id k B)
      (ModuleCat.uliftFlattenEquiv.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k N).toLinearMap n
      ((coefficientLiftEquiv k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n).symm
        (ULift.up (ULift.up (f m.down.down) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun i => g (a i)))))
  rw [coefficientLiftEquiv_symm_up_tprod, linearMap_tprod]
  rfl

/-- The homology of the whole lift of the tensor chain map is natural
for the coefficient-lift comparisons, with independent algebra universes. -/
theorem liftedMap_homology_wholeLift.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    let F : ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k ⥤ ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k :=
      ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k
    let eM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) :=
      coefficientLiftComplexIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
    let eN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) :=
      coefficientLiftComplexIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
    let γM : homology k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) n ≅
        F.obj (homology k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n) :=
      coefficientLiftHomologyIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n
    let γN : homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) n ≅
        F.obj (homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n) :=
      coefficientLiftHomologyIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n
    HomologicalComplex.homologyMap
        (eM.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (liftedMap g f hleft hright) ≫ eN.inv) n ≫ γN.hom =
      γM.hom ≫ F.map (HomologicalComplex.homologyMap (liftedMap g f hleft hright) n) := by
  dsimp only
  let F : ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k ⥤ ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k :=
    ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k
  let K : ChainComplex (ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k) ℕ :=
    chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
  let L : ChainComplex (ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k) ℕ :=
    chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k)
    (ComplexShape.down ℕ) n
  let H₀ := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k)
    (ComplexShape.down ℕ) n
  let φ : K ⟶ L := liftedMap g f hleft hright
  let eM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    coefficientLiftComplexIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
  let eN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L :=
    coefficientLiftComplexIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
  let γM : homology k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) n ≅
      F.obj (homology k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n) :=
    coefficientLiftHomologyIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n
  let γN : homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) n ≅
      F.obj (homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n) :=
    coefficientLiftHomologyIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n
  let cM : H.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
      F.obj (K.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app K
  let cN : H.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) ≅
      F.obj (L.homology n) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n F).app L
  have hm : γM.hom = H.map eM.hom ≫ cM.hom :=
    coefficientLiftHomologyIso_hom_eq k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n
  have hn : γN.hom = H.map eN.hom ≫ cN.hom :=
    coefficientLiftHomologyIso_hom_eq k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n
  have hpres : H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫ cN.hom =
      cM.hom ≫ F.map (HomologicalComplex.homologyMap φ n) := by
    have h :=
        (HomologicalComplex.mapHomologyFunctorIso
          (c := ComplexShape.down ℕ) n F).hom.naturality φ
    change H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫ cN.hom =
      cM.hom ≫ F.map (H₀.map φ) at h
    have hmap : H₀.map φ = HomologicalComplex.homologyMap φ n := by
      dsimp only [H₀]
      rw [HomologicalComplex.homologyFunctor_map]
    rw [hmap] at h
    exact h
  rw [← HomologicalComplex.homologyFunctor_map]
  change H.map (eM.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫ eN.inv) ≫
      γN.hom = γM.hom ≫ F.map (HomologicalComplex.homologyMap φ n)
  rw [hm, hn, H.map_comp, H.map_comp]
  have h₀ :
      ((H.map eM.hom ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
        H.map eN.inv) ≫ (H.map eN.hom ≫ cN.hom)) =
      (H.map eM.hom ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
        ((H.map eN.inv ≫ H.map eN.hom) ≫ cN.hom)) := by simp only [Category.assoc]
  have h₁ :
      (H.map eM.hom ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
        ((H.map eN.inv ≫ H.map eN.hom) ≫ cN.hom)) =
      (H.map eM.hom ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
        cN.hom) := by
      rw [← H.map_comp, Iso.inv_hom_id, H.map_id, Category.id_comp]
  have h₂ :
      (H.map eM.hom ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
        cN.hom) =
      (H.map eM.hom ≫ (cM.hom ≫ F.map (HomologicalComplex.homologyMap φ n))) := by
      rw [hpres]
  have h₃ :
      (H.map eM.hom ≫ (cM.hom ≫ F.map (HomologicalComplex.homologyMap φ n))) =
      ((H.map eM.hom ≫ cM.hom) ≫ F.map (HomologicalComplex.homologyMap φ n)) :=
    (Category.assoc _ _ _).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃)))

/-- The same whole-lift naturality on the original homology carriers. -/
theorem liftedMap_rawHomology_wholeLift.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    let F : ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k ⥤ ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k :=
      ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k
    let eM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) :=
      coefficientLiftComplexIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
    let eN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) :=
      coefficientLiftComplexIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
    (coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k B
        (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n).toLinearMap.comp
      (HomologicalComplex.homologyMap
        (eM.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (liftedMap g f hleft hright) ≫ eN.inv) n).hom =
    (HomologicalComplex.homologyMap (liftedMap g f hleft hright) n).hom.comp
      (coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k A
        (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n).toLinearMap := by
  dsimp only
  have hc := liftedMap_homology_wholeLift.{z₁} g f hleft hright n
  dsimp only at hc
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun α : homology k A
        (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) n ⟶
        (ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k).obj
          (homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n) => α.hom x) hc
  exact congrArg ULift.down hx

end LiftedMapHeightComparison

section RawHomologyMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N] [Module Bᵐᵒᵖ N]
  [SMulCommClass B Bᵐᵒᵖ N] [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The k-linear HH map on the original independent raw homology carriers.
Both carriers are lifted canonically only for the native homology map, then
returned by the constructed lift comparisons. No desired comparison is input. -/
def rawHomologyLinearMap (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) : (homology k A M n).carrier →ₗ[k] (homology k B N n).carrier := by
  let eM : homology k A (ULift.{max u v v' w w'} M) n ≅
      (ModuleCat.uliftFunctor.{max u v v' w w', max u v w} k).obj (homology k A M n) :=
    coefficientLiftHomologyIso k A M n
  let eN : homology k B (ULift.{max u v v' w w'} N) n ≅
      (ModuleCat.uliftFunctor.{max u v v' w w', max u v' w'} k).obj (homology k B N n) :=
    coefficientLiftHomologyIso k B N n
  let h : homology k A (ULift.{max u v v' w w'} M) n ⟶
      homology k B (ULift.{max u v v' w w'} N) n :=
    HomologicalComplex.homologyMap (liftedMap g f hleft hright) n
  exact (ULift.moduleEquiv : ULift.{max u v v' w w'} (homology k B N n).carrier ≃ₗ[k]
      (homology k B N n).carrier).toLinearMap.comp
    (eN.hom.hom.comp (h.hom.comp (eM.inv.hom.comp
      (ULift.moduleEquiv : ULift.{max u v v' w w'} (homology k A M n).carrier ≃ₗ[k]
        (homology k A M n).carrier).symm.toLinearMap)))

/-- Characteristic conjugation formula for the raw HH linear map. -/
theorem rawHomologyLinearMap_eq_conjugate (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    rawHomologyLinearMap g f hleft hright n =
      (coefficientLiftRawHomologyEquiv.{max u v v' w w'} k B N n).toLinearMap.comp
        ((HomologicalComplex.homologyMap (liftedMap g f hleft hright) n).hom.comp
          (coefficientLiftRawHomologyEquiv.{max u v v' w w'} k A M n).symm.toLinearMap) :=
  rfl

/-- The raw HH map computed at a specified canonical common lift height. -/
def rawHomologyLinearMapAt.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) : (homology k A M n).carrier →ₗ[k] (homology k B N n).carrier :=
  (coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k B N n).toLinearMap.comp
    ((HomologicalComplex.homologyMap (liftedMapAt.{z₁} g f hleft hright) n).hom.comp
      (coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k A M n).symm.toLinearMap)

@[simp]
theorem rawHomologyLinearMapAt_zero (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    rawHomologyLinearMapAt.{0} g f hleft hright n =
      rawHomologyLinearMap g f hleft hright n := rfl

/-- The raw HH map is independent of increasing the native common lift
height. The preimage used in the proof is the inverse of the homology
isomorphism induced by coefficient flattening. -/
theorem rawHomologyLinearMapAt_eq.{z₁, u₁, v₁, v₂, w₁, w₂}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    rawHomologyLinearMapAt.{z₁} g f hleft hright n =
      rawHomologyLinearMap g f hleft hright n := by
  let F : ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k ⥤ ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k :=
    ModuleCat.uliftFunctor.{max u₁ v₁ v₂ w₁ w₂ z₁, max u₁ v₁ v₂ w₁ w₂} k
  let K : ChainComplex (ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k) ℕ :=
    chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
  let L : ChainComplex (ModuleCat.{max u₁ v₁ v₂ w₁ w₂} k) ℕ :=
    chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u₁ v₁ v₂ w₁ w₂ z₁} k)
    (ComplexShape.down ℕ) n
  let eM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    coefficientLiftComplexIso k A (ULift.{max u₁ v₁ v₂ w₁ w₂} M)
  let eN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L :=
    coefficientLiftComplexIso k B (ULift.{max u₁ v₁ v₂ w₁ w₂} N)
  let qM : chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ≅
      chainComplex k A (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} M) :=
    coefficientFlattenComplexIso.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k A M
  let qN : chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} N)) ≅
      chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N) :=
    coefficientFlattenComplexIso.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k B N
  let φ : K ⟶ L := liftedMap g f hleft hright
  let ψ := liftedMapAt.{z₁} g f hleft hright
  let θ := eM.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫ eN.inv
  let aM := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k A M n
  let aN := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k B N n
  let bM := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂} k A M n
  let bN := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂} k B N n
  let cM := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k A
    (ULift.{max u₁ v₁ v₂ w₁ w₂} M) n
  let cN := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ w₁ w₂ z₁} k B
    (ULift.{max u₁ v₁ v₂ w₁ w₂} N) n
  have hchain : qM.hom ≫ ψ = θ ≫ qN.hom := by
    simpa only [θ, Category.assoc] using
      (liftedMapAt_flatten.{z₁} g f hleft hright)
  have hH : HomologicalComplex.homologyMap qM.hom n ≫ HomologicalComplex.homologyMap ψ n =
      HomologicalComplex.homologyMap θ n ≫ HomologicalComplex.homologyMap qN.hom n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg
      (fun α : chainComplex k A
          (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) ⟶
          chainComplex k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N) =>
        HomologicalComplex.homologyMap α n) hchain
  have hm : aM.toLinearMap.comp (HomologicalComplex.homologyMap qM.hom n).hom =
      bM.toLinearMap.comp cM.toLinearMap :=
    coefficientLiftRawHomologyEquiv_comp.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k A M n
  have hn : aN.toLinearMap.comp (HomologicalComplex.homologyMap qN.hom n).hom =
      bN.toLinearMap.comp cN.toLinearMap :=
    coefficientLiftRawHomologyEquiv_comp.{max u₁ v₁ v₂ w₁ w₂, max u₁ v₁ v₂ w₁ w₂ z₁} k B N n
  have hnat : cN.toLinearMap.comp (HomologicalComplex.homologyMap θ n).hom =
      (HomologicalComplex.homologyMap φ n).hom.comp cM.toLinearMap :=
    liftedMap_rawHomology_wholeLift.{z₁} g f hleft hright n
  let dM := H.mapIso qM
  have hdM : dM.hom = HomologicalComplex.homologyMap qM.hom n := by
    change H.map qM.hom = HomologicalComplex.homologyMap qM.hom n
    dsimp only [H]
    rw [HomologicalComplex.homologyFunctor_map]
  rw [rawHomologyLinearMap_eq_conjugate]
  unfold rawHomologyLinearMapAt
  apply LinearMap.ext
  intro x
  let y : (homology k A
      (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) n).carrier :=
    dM.inv.hom (aM.symm x)
  have hy₀ : dM.hom.hom y = aM.symm x := by
    have h := LinearEquiv.apply_symm_apply dM.toLinearEquiv (aM.symm x)
    exact h
  have hy : (HomologicalComplex.homologyMap qM.hom n).hom y = aM.symm x := by
    rw [← hdM]
    exact hy₀
  have hc : cM y = bM.symm x := by
    apply bM.injective
    calc
      bM (cM y) = aM ((HomologicalComplex.homologyMap qM.hom n).hom y) :=
        (LinearMap.congr_fun hm y).symm
      _ = x := (congrArg aM hy).trans (LinearEquiv.apply_symm_apply aM x)
      _ = bM (bM.symm x) := (LinearEquiv.apply_symm_apply bM x).symm
  have hcoord : (HomologicalComplex.homologyMap ψ n).hom
        ((HomologicalComplex.homologyMap qM.hom n).hom y) =
      (HomologicalComplex.homologyMap qN.hom n).hom
        ((HomologicalComplex.homologyMap θ n).hom y) :=
    congrArg
      (fun α : homology k A
          (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} (ULift.{max u₁ v₁ v₂ w₁ w₂} M)) n ⟶
          homology k B (ULift.{max u₁ v₁ v₂ w₁ w₂ z₁} N) n => α.hom y) hH
  change aN ((HomologicalComplex.homologyMap ψ n).hom (aM.symm x)) =
    bN ((HomologicalComplex.homologyMap φ n).hom (bM.symm x))
  calc
    aN ((HomologicalComplex.homologyMap ψ n).hom (aM.symm x)) =
        aN ((HomologicalComplex.homologyMap ψ n).hom
          ((HomologicalComplex.homologyMap qM.hom n).hom y)) :=
      congrArg (fun z₁ => aN ((HomologicalComplex.homologyMap ψ n).hom z₁)) hy.symm
    _ = aN ((HomologicalComplex.homologyMap qN.hom n).hom
        ((HomologicalComplex.homologyMap θ n).hom y)) := congrArg aN hcoord
    _ = bN (cN ((HomologicalComplex.homologyMap θ n).hom y)) :=
      LinearMap.congr_fun hn ((HomologicalComplex.homologyMap θ n).hom y)
    _ = bN ((HomologicalComplex.homologyMap φ n).hom (cM y)) :=
      congrArg bN (LinearMap.congr_fun hnat y)
    _ = bN ((HomologicalComplex.homologyMap φ n).hom (bM.symm x)) :=
      congrArg (fun z₁ => bN ((HomologicalComplex.homologyMap φ n).hom z₁)) hc

end RawHomologyMaps


section RawHomologyAtLaws

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]
  {P : Type w''} [AddCommGroup P] [Module k P]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
  [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
  [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
  [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]

/-- Raw-carrier identity is independent of the canonical lift height. -/
@[simp]
theorem rawHomologyLinearMapAt_id.{z₁, u₁, v₁, w₁}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    (n : ℕ) :
    rawHomologyLinearMapAt.{z₁} (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
      (fun _ _ => rfl) (fun _ _ => rfl) n = LinearMap.id := by
  unfold rawHomologyLinearMapAt
  rw [liftedMapAt_id, HomologicalComplex.homologyMap_id]
  apply LinearMap.ext
  intro x
  change (coefficientLiftRawHomologyEquiv.{max u₁ v₁ w₁ z₁} k A M n)
    ((coefficientLiftRawHomologyEquiv.{max u₁ v₁ w₁ z₁} k A M n).symm x) = x
  exact LinearEquiv.apply_symm_apply _ x

/-- Raw-carrier maps compose at the common upper lift height. No coefficient or
algebra universe is identified with any other universe. -/
theorem rawHomologyLinearMapAt_comp.{z₁, u₁, v₁, v₂, v₃, w₁, w₂, w₃}
    {k : Type u₁} [CommRing k]
    {A : Type v₁} [Ring A] [Algebra k A]
    {B : Type v₂} [Ring B] [Algebra k B]
    {C : Type v₃} [Ring C] [Algebra k C]
    {M : Type w₁} [AddCommGroup M] [Module k M]
    [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
    [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
    [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
    {N : Type w₂} [AddCommGroup N] [Module k N]
    [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
    [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
    [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
    {P : Type w₃} [AddCommGroup P] [Module k P]
    [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
    [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
    [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]
    (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (hleft' : ∀ b n, f' (b • n) = h b • f' n)
    (hright' : ∀ b n, f' (MulOpposite.op b • n) = MulOpposite.op (h b) • f' n)
    (n : ℕ) :
    (rawHomologyLinearMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} h f' hleft' hright' n).comp
        (rawHomologyLinearMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} g f hleft hright n) =
      rawHomologyLinearMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} (h.comp g) (f'.comp f)
        (fun a m => (congrArg f' (hleft a m)).trans (hleft' (g a) (f m)))
        (fun a m => (congrArg f' (hright a m)).trans (hright' (g a) (f m))) n := by
  let eM := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} k A M n
  let eN := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} k B N n
  let eP := coefficientLiftRawHomologyEquiv.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} k C P n
  let φ : chainComplex k A (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M) ⟶
      chainComplex k B (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} N) :=
    liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} g f hleft hright
  let ψ : chainComplex k B (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} N) ⟶
      chainComplex k C (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P) :=
    liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} h f' hleft' hright'
  let χ : chainComplex k A (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M) ⟶
      chainComplex k C (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P) :=
    liftedMapAt.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} (h.comp g) (f'.comp f)
    (fun a m => (congrArg f' (hleft a m)).trans (hleft' (g a) (f m)))
    (fun a m => (congrArg f' (hright a m)).trans (hright' (g a) (f m)))
  have hc : HomologicalComplex.homologyMap φ n ≫ HomologicalComplex.homologyMap ψ n =
      HomologicalComplex.homologyMap χ n := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg
      (fun α : chainComplex k A (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M) ⟶
          chainComplex k C (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P) =>
        HomologicalComplex.homologyMap α n)
      (liftedMapAt_comp.{z₁} g h f f' hleft hright hleft' hright')
  apply LinearMap.ext
  intro x
  change eP ((HomologicalComplex.homologyMap ψ n).hom
      (eN.symm (eN ((HomologicalComplex.homologyMap φ n).hom (eM.symm x))))) =
    eP ((HomologicalComplex.homologyMap χ n).hom (eM.symm x))
  have hcancel := LinearEquiv.symm_apply_apply eN
    ((HomologicalComplex.homologyMap φ n).hom (eM.symm x))
  exact (congrArg
    (fun y : (homology k B (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} N) n).carrier =>
      eP ((HomologicalComplex.homologyMap ψ n).hom y)) hcancel).trans
    (congrArg eP (congrArg
      (fun α : homology k A (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} M) n ⟶
          homology k C (ULift.{max u₁ v₁ v₂ v₃ w₁ w₂ w₃ z₁} P) n =>
        α.hom (eM.symm x)) hc))

/-- The raw HH maps compose across independent coefficient and algebra
universes. This follows from the common-height native maps and the lift-height independence, with no desired comparison supplied by a caller. -/
theorem rawHomologyLinearMap_comp (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (hleft' : ∀ b n, f' (b • n) = h b • f' n)
    (hright' : ∀ b n, f' (MulOpposite.op b • n) = MulOpposite.op (h b) • f' n)
    (n : ℕ) :
    (rawHomologyLinearMap h f' hleft' hright' n).comp
        (rawHomologyLinearMap g f hleft hright n) =
      rawHomologyLinearMap (h.comp g) (f'.comp f)
        (fun a m => (congrArg f' (hleft a m)).trans (hleft' (g a) (f m)))
        (fun a m => (congrArg f' (hright a m)).trans (hright' (g a) (f m))) n := by
  have hcomp := rawHomologyLinearMapAt_comp.{0} g h f f' hleft hright hleft' hright' n
  simpa only [rawHomologyLinearMapAt_eq] using hcomp

end RawHomologyAtLaws

section RawHomologyCommonUniverseLaws

variable {k : Type u} [CommRing k]
  {A B C : Type v} [Ring A] [Ring B] [Ring C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  {M N P : Type w} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N] [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]
  [Module C P] [Module Cᵐᵒᵖ P] [SMulCommClass C Cᵐᵒᵖ P]
  [SMulCommClass k C P] [SMulCommClass k Cᵐᵒᵖ P]
  [IsScalarTower k C P] [IsScalarTower k Cᵐᵒᵖ P]

/-- In a common carrier category the raw HH linear map is exactly the native
homology map, rather than a second action on the homology carrier. -/
theorem rawHomologyLinearMap_eq_native (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    rawHomologyLinearMap g f hleft hright n =
      (HomologicalComplex.homologyMap (mapInSameUniverse g f hleft hright) n).hom := by
  let F : ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w} k :=
    ModuleCat.uliftFunctor.{max u v w, max u v w} k
  let eM : homology k A (ULift.{max u v w} M) n ≅ F.obj (homology k A M n) :=
    coefficientLiftHomologyIso k A M n
  let eN : homology k B (ULift.{max u v w} N) n ≅ F.obj (homology k B N n) :=
    coefficientLiftHomologyIso k B N n
  let h : homology k A (ULift.{max u v w} M) n ⟶
      homology k B (ULift.{max u v w} N) n :=
    HomologicalComplex.homologyMap (liftedMap g f hleft hright) n
  let b : homology k A M n ⟶ homology k B N n :=
    HomologicalComplex.homologyMap (mapInSameUniverse g f hleft hright) n
  have hnat : h ≫ eN.hom = eM.hom ≫ F.map b := by
    have hh := coefficientLiftHomologyIso_naturality.{max u v w}
      g f hleft hright n
    dsimp only [homologyMap] at hh
    simp only [HomologicalComplex.homologyFunctor_map] at hh
    have hm : mapInSameUniverse g
        (show ULift.{max u v w} M →ₗ[k] ULift.{max u v w} N from liftLinearMap f)
        (fun a m => congrArg ULift.up (hleft a m.down))
        (fun a m => congrArg ULift.up (hright a m.down)) =
        liftedMap g f hleft hright := by
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      erw [mapInSameUniverse_f]
      rfl
    simpa only [hm] using hh
  have hrec : eM.inv ≫ h ≫ eN.hom = F.map b := by
    calc
      eM.inv ≫ h ≫ eN.hom = eM.inv ≫ (eM.hom ≫ F.map b) :=
        congrArg (fun q => eM.inv ≫ q) hnat
      _ = F.map b := by rw [Iso.inv_hom_id_assoc]
  apply LinearMap.ext
  intro x
  change (eN.hom.hom (h.hom (eM.inv.hom (ULift.up x)))).down = b.hom x
  have hx := congrArg
    (fun q : F.obj (homology k A M n) ⟶ F.obj (homology k B N n) =>
      q.hom (ULift.up x)) hrec
  exact congrArg ULift.down hx

/-- The raw map agrees with the public common-universe HH homology morphism. -/
theorem rawHomologyLinearMap_eq_homologyMap (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hleft : ∀ a m, f (a • m) = g a • f m)
    (hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m)
    (n : ℕ) :
    rawHomologyLinearMap g f hleft hright n = (homologyMap g f hleft hright n).hom := by
  unfold homologyMap
  rw [HomologicalComplex.homologyFunctor_map]
  exact rawHomologyLinearMap_eq_native g f hleft hright n

/-- Identity maps act as the identity on the raw HH carrier. -/
@[simp]
theorem rawHomologyLinearMap_id (n : ℕ) :
    rawHomologyLinearMap (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
      (fun _ _ => rfl) (fun _ _ => rfl) n = LinearMap.id := by
  change rawHomologyLinearMapAt.{0} (NonUnitalAlgHom.id k A)
    (LinearMap.id : M →ₗ[k] M) (fun _ _ => rfl) (fun _ _ => rfl) n = LinearMap.id
  exact rawHomologyLinearMapAt_id.{0} (k := k) (A := A) (M := M) n

end RawHomologyCommonUniverseLaws

section CoefficientEndomorphisms

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  {S : Type w'} [Semiring S]

/-- An actual commuting coefficient-ring action acts on the Hochschild complex. -/
def coefficientEndRingHom (ρ : S →+* Module.End k M)
    (hleft : ∀ (s : S) (a : A) (m : M), ρ s (a • m) = a • ρ s m)
    (hright : ∀ (s : S) (a : A) (m : M),
      ρ s (MulOpposite.op a • m) = MulOpposite.op a • ρ s m) :
    S →+* End (chainComplex k A M) where
  toFun s := End.of (mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ s) (hleft s) (hright s))
  map_one' := by
    apply End.ext
    change mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ 1) (hleft 1) (hright 1) = 𝟙 _
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      HomologicalComplex.zero_f, HomologicalComplex.add_f_apply,
      ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero, ModuleCat.hom_add]
    erw [mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A) (ρ 1) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m ⊗ₜ[k] PiTensorProduct.tprod k a
    rw [linearMap_tprod, map_one]
    rfl
  map_mul' s t := by
    apply End.ext
    change mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ (s * t))
        (hleft (s * t)) (hright (s * t)) =
      mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ t) (hleft t) (hright t) ≫
        mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ s) (hleft s) (hright s)
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      HomologicalComplex.zero_f, HomologicalComplex.add_f_apply,
      ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero, ModuleCat.hom_add]
    erw [mapInSameUniverse_f, mapInSameUniverse_f, mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A) (ρ (s * t)) n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      linearMap (NonUnitalAlgHom.id k A) (ρ s) n
        (linearMap (NonUnitalAlgHom.id k A) (ρ t) n
          (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    simp only [linearMap_tprod, map_mul]
    rfl
  map_zero' := by
    apply End.ext
    change mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ 0) (hleft 0) (hright 0) = 0
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      HomologicalComplex.zero_f, HomologicalComplex.add_f_apply,
      ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero, ModuleCat.hom_add]
    erw [mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A) (ρ 0) n
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0
    rw [linearMap_tprod, map_zero]
    simp only [LinearMap.zero_apply, TensorProduct.zero_tmul]
  map_add' s t := by
    apply End.ext
    change mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ (s + t))
        (hleft (s + t)) (hright (s + t)) =
      mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ s) (hleft s) (hright s) +
        mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ t) (hleft t) (hright t)
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      HomologicalComplex.zero_f, HomologicalComplex.add_f_apply,
      ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero, ModuleCat.hom_add]
    erw [mapInSameUniverse_f, mapInSameUniverse_f, mapInSameUniverse_f]
    apply tensorPower_ext
    intro m a
    change linearMap (NonUnitalAlgHom.id k A) (ρ (s + t)) n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      linearMap (NonUnitalAlgHom.id k A) (ρ s) n (m ⊗ₜ[k] PiTensorProduct.tprod k a) +
        linearMap (NonUnitalAlgHom.id k A) (ρ t) n (m ⊗ₜ[k] PiTensorProduct.tprod k a)
    simp only [linearMap_tprod, map_add, LinearMap.add_apply]
    exact TensorProduct.add_tmul _ _ _

theorem coefficientEndRingHom_f_tprod (ρ : S →+* Module.End k M)
    (hleft : ∀ (s : S) (a : A) (m : M), ρ s (a • m) = a • ρ s m)
    (hright : ∀ (s : S) (a : A) (m : M),
      ρ s (MulOpposite.op a • m) = MulOpposite.op a • ρ s m)
    (s : S) (n : ℕ) (m : M) (a : Fin n → A) :
    (((coefficientEndRingHom ρ hleft hright s).asHom).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = ρ s m ⊗ₜ[k] PiTensorProduct.tprod k a := by
  change ((mapInSameUniverse (NonUnitalAlgHom.id k A) (ρ s)
      (hleft s) (hright s)).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  exact (LinearMap.congr_fun
    (mapInSameUniverse_f (NonUnitalAlgHom.id k A) (ρ s) (hleft s) (hright s) n)
    (m ⊗ₜ[k] PiTensorProduct.tprod k a)).trans
      (linearMap_tprod (NonUnitalAlgHom.id k A) (ρ s) n m a)

/-- Native `Functor.mapEnd` and additivity transfer that action to homology. -/
def coefficientHomologyEndRingHom (ρ : S →+* Module.End k M)
    (hleft : ∀ (s : S) (a : A) (m : M), ρ s (a • m) = a • ρ s m)
    (hright : ∀ (s : S) (a : A) (m : M),
      ρ s (MulOpposite.op a • m) = MulOpposite.op a • ρ s m)
    (n : ℕ) : S →+* End (homology k A M n) :=
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) n
  { (F.mapEnd (X := chainComplex k A M)).comp
      (coefficientEndRingHom ρ hleft hright).toMonoidHom with
    map_zero' := by
      apply End.ext
      change F.map ((coefficientEndRingHom ρ hleft hright) 0).asHom = 0
      rw [map_zero]
      change F.map (0 : chainComplex k A M ⟶ chainComplex k A M) = 0
      exact F.map_zero _ _
    map_add' s t := by
      apply End.ext
      change F.map ((coefficientEndRingHom ρ hleft hright) (s + t)).asHom =
        F.map ((coefficientEndRingHom ρ hleft hright) s).asHom +
          F.map ((coefficientEndRingHom ρ hleft hright) t).asHom
      rw [map_add]
      exact F.map_add }

/-- The coefficient-valued module on the native homology carrier. -/
abbrev coefficientHomologyModule (ρ : S →+* Module.End k M)
    (hleft : ∀ (s : S) (a : A) (m : M), ρ s (a • m) = a • ρ s m)
    (hright : ∀ (s : S) (a : A) (m : M),
      ρ s (MulOpposite.op a • m) = MulOpposite.op a • ρ s m)
    (n : ℕ) : Module S (homology k A M n).carrier :=
  Module.compHom (homology k A M n).carrier
    ((ModuleCat.endRingEquiv (homology k A M n)).toRingHom.comp
      (coefficientHomologyEndRingHom ρ hleft hright n))

end CoefficientEndomorphisms

end ModuleCat.Algebra.Hochschild
