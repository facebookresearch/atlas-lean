/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Exterior-power functors and scalar extension

Let `R` be a commutative ring. The exterior-power functor sends an `R`-module `M` to `⋀ⁿ[R] M`
and a linear map `f` to the map sending `m₁ ∧ ⋯ ∧ mₙ` to `f(m₁) ∧ ⋯ ∧ f(mₙ)`. Degree zero is
naturally the regular module `R`, and degree one is naturally `M`.

For a commutative `R`-algebra `S`, exterior base change gives a natural isomorphism `S ⊗[R]
⋀ⁿ[R] M ≅ ⋀ⁿ[S] (S ⊗[R] M)`. It sends `s ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to `s • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ))`.
The scalar rings and module carrier have independent universes; the functor targets include
their joint universe.

Reference: Bourbaki, *Algebra*, Chapter III, for exterior powers and extension of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The exterior-power functor in a joint scalar-module universe.

For modules with carrier universe `max u v`, the `n`th exterior-power functor has source and
target in that same universe. -/
abbrev exteriorPowerFunctor (n : ℕ) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  ModuleCat.exteriorPower.functor.{max u v, u} R n

/-- The natural comparison in exterior degree one.

The degree-one exterior-power functor on the joint-universe module category is naturally
isomorphic to the identity functor. -/
def exteriorPowerOneNatIso :
    exteriorPowerFunctor.{u, v} R 1 ≅ 𝟭 (ModuleCat.{max u v} R) :=
  NatIso.ofComponents
    (fun M => (exteriorPower.oneEquiv R M).toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      exact exteriorPower.oneEquiv_naturality f.hom)

variable (S : Type w) [CommRing S] [Algebra R S]

/-- The tensor description of extension of scalars.

For a commutative `R`-algebra `S` and an `R`-module `M`, extension along `algebraMap R S` is
`S`-linearly equivalent to `S ⊗[R] M`, with both tensor-factor values retained. -/
def scalarExtensionToTensorEquiv (M : ModuleCat.{v} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M := by
  let φ := algebraMap R S
  have hA : φ.toAlgebra = ‹Algebra R S› := toAlgebra_algebraMap
  let SR : ModuleCat.{w} R :=
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  letI : Module S SR := (ModuleCat.of S S).isModule
  letI : Module R SR := SR.isModule
  have hScalar (r : R) (s : S) : r • s = φ r * s :=
    (congrArg (fun a : Algebra R S => @SMul.smul R S a.toSMul r s) hA).symm
  let : IsScalarTower R S SR := by
    refine ⟨?_⟩
    intro r s x
    change (r • s) * (show S from x) = φ r * (s * (show S from x))
    rw [hScalar, mul_assoc]
  let eS : SR ≃ₗ[S] S :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := TensorProduct.AlgebraTensorModule.congr eS (LinearEquiv.refl R M)
  exact
    { toFun := fun x => e x
      invFun := fun x => e.symm x
      left_inv := fun x => e.symm_apply_apply x
      right_inv := fun x => e.apply_symm_apply x
      map_add' := fun x y => e.map_add x y
      map_smul' := fun s x => e.map_smul s x }

/-- The pure-tensor formula for scalar extension.

The scalar-extension equivalence sends the class represented by `s ⊗ m` in extension of
scalars to the same pure tensor in `S ⊗[R] M`. -/
theorem scalarExtensionToTensorEquiv_tmul (M : ModuleCat.{v} R) (s : S) (m : M) :
    scalarExtensionToTensorEquiv R S M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := by
  rfl

/-- The inverse pure-tensor formula for scalar extension.

The inverse equivalence sends `s ⊗ m ∈ S ⊗[R] M` to the same representative in extension of
scalars along `R → S`. -/
theorem scalarExtensionToTensorEquiv_symm_tmul (M : ModuleCat.{v} R) (s : S) (m : M) :
    (scalarExtensionToTensorEquiv R S M).symm (s ⊗ₜ[R] m) =
      s ⊗ₜ[R, algebraMap R S] m := by
  rfl

/-- The module component of exterior base change.

For a commutative `R`-algebra `S`, this is the `S`-module isomorphism from extension of
scalars of `⋀ⁿ[R] M` to `⋀ⁿ[S]` of the extended module. The common carrier universe includes
both scalar rings and `M`. -/
def exteriorPowerBaseChangeComponent (n : ℕ) (M : ModuleCat.{max u v w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((ModuleCat.exteriorPower.functor.{max u v w, u} R n).obj M) ≅
      (ModuleCat.exteriorPower.functor.{max u v w, w} S n).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  let Q := (ModuleCat.exteriorPower.functor.{max u v w, u} R n).obj M
  let P := (ModuleCat.extendScalars (algebraMap R S)).obj M
  let q : Q ≃ₗ[R] (⋀[R]^n M) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eSource := (scalarExtensionToTensorEquiv R S Q).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) q)
  let ePower : (⋀[S]^n P) ≃ₗ[S]
      (ModuleCat.exteriorPower.functor.{max u v w, w} S n).obj P :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eTarget := (exteriorPower.mapEquiv S (S ⊗[R] M) n
    (scalarExtensionToTensorEquiv R S M).symm).trans ePower
  exact (eSource.trans ((exteriorPower.baseChangeEquiv R S M n).trans eTarget)).toModuleIso

/-- The component formula for exterior base change.

The forward component sends `s ⊗ (a₀ ∧ ⋯ ∧ a_(n-1))` to `s • ((1 ⊗ a₀) ∧ ⋯ ∧ (1 ⊗ a_(n-1)))`
in the exterior power over `S`. -/
theorem exteriorPowerBaseChangeComponent_hom_tmul_ιMulti (n : ℕ)
    (M : ModuleCat.{max u v w} R) (s : S) (a : Fin n → M) :
    ((exteriorPowerBaseChangeComponent.{u, v, w} R S n M).hom).hom
        (s ⊗ₜ[R, algebraMap R S] exteriorPower.ιMulti R n a) =
      s • exteriorPower.ιMulti S n
        (M := (ModuleCat.extendScalars (algebraMap R S)).obj M)
        (fun i => (1 : S) ⊗ₜ[R, algebraMap R S] a i) := by
  let Q := (ModuleCat.exteriorPower.functor.{max u v w, u} R n).obj M
  let P := (ModuleCat.extendScalars (algebraMap R S)).obj M
  let q : Q ≃ₗ[R] (⋀[R]^n M) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eSource := (scalarExtensionToTensorEquiv R S Q).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) q)
  let ePower : (⋀[S]^n P) ≃ₗ[S]
      (ModuleCat.exteriorPower.functor.{max u v w, w} S n).obj P :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eTarget := (exteriorPower.mapEquiv S (S ⊗[R] M) n
    (scalarExtensionToTensorEquiv R S M).symm).trans ePower
  let aQ : Q := exteriorPower.ιMulti R n a
  let x : (ModuleCat.extendScalars (algebraMap R S)).obj Q :=
    s ⊗ₜ[R, algebraMap R S] aQ
  have h₀ : scalarExtensionToTensorEquiv R S Q x = s ⊗ₜ[R] aQ :=
    scalarExtensionToTensorEquiv_tmul R S Q s aQ
  have h₁ : TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) q
      (s ⊗ₜ[R] aQ) = s ⊗ₜ[R] exteriorPower.ιMulti R n a := by
    exact (TensorProduct.AlgebraTensorModule.congr_tmul
      (LinearEquiv.refl S S) q s aQ).trans rfl
  have hSource : eSource x = s ⊗ₜ[R] exteriorPower.ιMulti R n a :=
    (show eSource x = TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) q
        (scalarExtensionToTensorEquiv R S Q x) from rfl).trans
      ((congrArg (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) q) h₀).trans h₁)
  have hTarget : eTarget
      (s • exteriorPower.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i)) =
      s • exteriorPower.ιMulti S n (M := P)
        (fun i => (1 : S) ⊗ₜ[R, algebraMap R S] a i) := by
    change exteriorPower.mapEquiv S (S ⊗[R] M) n
        (scalarExtensionToTensorEquiv R S M).symm
        (s • exteriorPower.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i)) = _
    rw [map_smul, exteriorPower.mapEquiv_apply_ιMulti]
    apply congrArg (fun v => s • exteriorPower.ιMulti S n v)
    funext i
    exact scalarExtensionToTensorEquiv_symm_tmul R S M (1 : S) (a i)
  change eTarget (exteriorPower.baseChangeEquiv R S M n (eSource x)) = _
  exact (congrArg eTarget (congrArg (exteriorPower.baseChangeEquiv R S M n) hSource)).trans
    ((congrArg eTarget (exteriorPower.baseChangeEquiv_apply_tmul_ιMulti R S M n s a)).trans hTarget)

/-- The inverse component formula for exterior base change.

The inverse component sends `s • ((1 ⊗ a₀) ∧ ⋯ ∧ (1 ⊗ a_(n-1)))` to `s ⊗ (a₀ ∧ ⋯ ∧ a_(n-1))`
in the extended exterior power over `R`. -/
theorem exteriorPowerBaseChangeComponent_inv_word (n : ℕ)
    (M : ModuleCat.{max u v w} R) (s : S) (a : Fin n → M) :
    ((exteriorPowerBaseChangeComponent.{u, v, w} R S n M).inv).hom
        (s • exteriorPower.ιMulti S n
          (M := (ModuleCat.extendScalars (algebraMap R S)).obj M)
          (fun i => (1 : S) ⊗ₜ[R, algebraMap R S] a i)) =
      s ⊗ₜ[R, algebraMap R S] exteriorPower.ιMulti R n a := by
  let e := exteriorPowerBaseChangeComponent.{u, v, w} R S n M
  have h := exteriorPowerBaseChangeComponent_hom_tmul_ιMulti.{u, v, w} R S n M s a
  exact (congrArg e.inv.hom h).symm.trans
    (ModuleCat.inv_hom_apply e (s ⊗ₜ[R, algebraMap R S] exteriorPower.ιMulti R n a))

/-- The natural isomorphism of exterior powers and scalar extension.

For every `n ∈ ℕ`, taking the `n`th exterior power over `R` and then extending to `S` is
naturally isomorphic to extending first and taking the exterior power over `S`. -/
def exteriorPowerBaseChangeNatIso (n : ℕ) :
    ModuleCat.exteriorPower.functor.{max u v w, u} R n ⋙
        ModuleCat.extendScalars (algebraMap R S) ≅
      ModuleCat.extendScalars (algebraMap R S) ⋙
        ModuleCat.exteriorPower.functor.{max u v w, w} S n := by
  let φ := algebraMap R S
  refine NatIso.ofComponents (exteriorPowerBaseChangeComponent.{u, v, w} R S n) ?_
  intro M N f
  dsimp only [Functor.comp_obj]
  apply ModuleCat.hom_ext
  let Q := (ModuleCat.exteriorPower.functor.{max u v w, u} R n).obj M
  let T := (ModuleCat.exteriorPower.functor.{max u v w, w} S n).obj
    ((ModuleCat.extendScalars φ).obj N)
  let SR : ModuleCat.{w} R := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let : Module S SR := (ModuleCat.of S S).isModule
  let : Module R SR := SR.isModule
  let : IsScalarTower R S SR := IsScalarTower.of_compHom R S SR
  let : Module S T := T.isModule
  let : Module R T := Module.compHom T φ
  let : IsScalarTower R S T := IsScalarTower.of_compHom R S T
  let L := ((ModuleCat.extendScalars φ).map
      ((ModuleCat.exteriorPower.functor.{max u v w, u} R n).map f) ≫
    (exteriorPowerBaseChangeComponent.{u, v, w} R S n N).hom).hom
  let H := ((exteriorPowerBaseChangeComponent.{u, v, w} R S n M).hom ≫
    (ModuleCat.exteriorPower.functor.{max u v w, w} S n).map
      ((ModuleCat.extendScalars φ).map f)).hom
  let C := (ModuleCat.extendScalars φ).obj Q
  let eInput : SR ⊗[R] Q ≃ₗ[S] C :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hInput (s : SR) (q : Q) :
      eInput (s ⊗ₜ[R] q) = (show C from (show S from s) ⊗ₜ[R, φ] q) := rfl
  let L₀ : SR ⊗[R] Q →ₗ[S] T := L.comp eInput.toLinearMap
  let H₀ : SR ⊗[R] Q →ₗ[S] T := H.comp eInput.toLinearMap
  have h : L₀ = H₀ := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext
    intro s
    apply exteriorPower.linearMap_ext
    apply _root_.AlternatingMap.ext
    intro a
    let aQ : Q := exteriorPower.ιMulti R n a
    let QN := (ModuleCat.exteriorPower.functor.{max u v w, u} R n).obj N
    let bQ : QN := exteriorPower.ιMulti R n (fun i => f.hom (a i))
    let u : C := (show S from s) ⊗ₜ[R, φ] aQ
    let g₀ := (ModuleCat.exteriorPower.functor.{max u v w, u} R n).map f
    let g₁ := (ModuleCat.extendScalars φ).map f
    let eM := exteriorPowerBaseChangeComponent.{u, v, w} R S n M
    let eN := exteriorPowerBaseChangeComponent.{u, v, w} R S n N
    let vM : Fin n → (ModuleCat.extendScalars φ).obj M :=
      fun i => (1 : S) ⊗ₜ[R, φ] a i
    let vN : Fin n → (ModuleCat.extendScalars φ).obj N :=
      fun i => (1 : S) ⊗ₜ[R, φ] f.hom (a i)
    have hF : ((ModuleCat.extendScalars φ).map g₀).hom u =
        (show S from s) ⊗ₜ[R, φ] bQ := by
      have ht := ModuleCat.ExtendScalars.map_tmul φ g₀ (show S from s) aQ
      have hg : g₀.hom aQ = bQ := exteriorPower.map_apply_ιMulti f.hom a
      exact ht.trans (congrArg (fun z : QN => (show S from s) ⊗ₜ[R, φ] z) hg)
    have hN : eN.hom.hom ((show S from s) ⊗ₜ[R, φ] bQ) =
        (show S from s) • exteriorPower.ιMulti S n vN :=
      exteriorPowerBaseChangeComponent_hom_tmul_ιMulti.{u, v, w} R S n N
        (show S from s) (fun i => f.hom (a i))
    have hM : eM.hom.hom u = (show S from s) • exteriorPower.ιMulti S n vM :=
      exteriorPowerBaseChangeComponent_hom_tmul_ιMulti.{u, v, w} R S n M (show S from s) a
    have hg₁ : ∀ i, g₁.hom (vM i) = vN i :=
      fun i => ModuleCat.ExtendScalars.map_tmul φ f (1 : S) (a i)
    have hLeft : L u = (show S from s) • exteriorPower.ιMulti S n vN :=
      (ModuleCat.comp_apply ((ModuleCat.extendScalars φ).map g₀) eN.hom u).trans
        ((congrArg eN.hom.hom hF).trans hN)
    have hRight : H u = (show S from s) • exteriorPower.ιMulti S n vN := by
      have ht := ModuleCat.comp_apply eM.hom
        ((ModuleCat.exteriorPower.functor.{max u v w, w} S n).map g₁) u
      have hs := ((ModuleCat.exteriorPower.functor.{max u v w, w} S n).map g₁).hom.map_smul
        (show S from s) (exteriorPower.ιMulti S n vM)
      have hw := exteriorPower.map_apply_ιMulti g₁.hom vM
      have hv : (fun i => g₁.hom (vM i)) = vN := funext hg₁
      exact ht.trans ((congrArg ((ModuleCat.exteriorPower.functor S n).map g₁).hom hM).trans
        (hs.trans ((congrArg (fun z => (show S from s) • z) hw).trans
          (congrArg (fun v => (show S from s) • exteriorPower.ιMulti S n v) hv))))
    change L (eInput (s ⊗ₜ[R] aQ)) = H (eInput (s ⊗ₜ[R] aQ))
    have hx : eInput (s ⊗ₜ[R] aQ) = u := hInput s aQ
    exact (congrArg L hx).trans ((hLeft.trans hRight.symm).trans (congrArg H hx).symm)
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun h (eInput.symm x)
  dsimp only [L₀, H₀] at hx
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] at hx
  exact hx

/-- The natural exterior base-change map on a pure wedge tensor.

At a module `M`, the forward natural comparison sends `s ⊗ (a₀ ∧ ⋯ ∧ a_(n-1))` to `s • ((1 ⊗
a₀) ∧ ⋯ ∧ (1 ⊗ a_(n-1)))`. -/
@[simp]
theorem exteriorPowerBaseChangeNatIso_hom_tmul_ιMulti (n : ℕ)
    (M : ModuleCat.{max u v w} R) (s : S) (a : Fin n → M) :
    ((exteriorPowerBaseChangeNatIso.{u, v, w} R S n).hom.app M).hom
        (s ⊗ₜ[R, algebraMap R S] exteriorPower.ιMulti R n a) =
      s • exteriorPower.ιMulti S n
        (M := (ModuleCat.extendScalars (algebraMap R S)).obj M)
        (fun i => (1 : S) ⊗ₜ[R, algebraMap R S] a i) :=
  by
    dsimp only [exteriorPowerBaseChangeNatIso, NatIso.ofComponents]
    exact exteriorPowerBaseChangeComponent_hom_tmul_ιMulti.{u, v, w} R S n M s a

/-- The inverse natural exterior base-change map on a wedge word.

At a module `M`, the inverse natural comparison sends the scaled wedge of `1 ⊗ a_i` to the
tensor of the wedge of the `a_i`. -/
@[simp]
theorem exteriorPowerBaseChangeNatIso_inv_word (n : ℕ)
    (M : ModuleCat.{max u v w} R) (s : S) (a : Fin n → M) :
    ((exteriorPowerBaseChangeNatIso.{u, v, w} R S n).inv.app M).hom
        (s • exteriorPower.ιMulti S n
          (M := (ModuleCat.extendScalars (algebraMap R S)).obj M)
          (fun i => (1 : S) ⊗ₜ[R, algebraMap R S] a i)) =
      s ⊗ₜ[R, algebraMap R S] exteriorPower.ιMulti R n a :=
  by
    dsimp only [exteriorPowerBaseChangeNatIso, NatIso.ofComponents]
    exact exteriorPowerBaseChangeComponent_inv_word.{u, v, w} R S n M s a

end ModuleCat

end
