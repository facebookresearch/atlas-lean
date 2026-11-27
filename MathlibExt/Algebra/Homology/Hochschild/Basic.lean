/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.TensorMonad
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The coefficient Hochschild complex

The tensor monad and the two actions of a bimodule construct its
Hochschild simplicial object. Its degree-n tensor coordinates are
M ⊗[k] TensorPower(k, n, R). Faces use the bimodule actions and adjacent
multiplication; degeneracies insert the algebra unit.

References: Weibel, Homological Algebra, §9.1; Loday, Cyclic Homology, §1.1.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicTopology
open scoped TensorProduct ModuleCat.Algebra ZeroObject

universe u v w

namespace ModuleCat.Algebra.Hochschild

attribute [local instance] underlyingSMulCommClass

variable {R : Type v}

/-- Remove the first entry from a tensor tuple. -/
def hochschildDropFirst {n : ℕ} (r : Fin (n + 1) → R) : Fin n → R :=
  fun j => r j.succ

/-- Remove the last entry from a tensor tuple. -/
def hochschildDropLast {n : ℕ} (r : Fin (n + 1) → R) : Fin n → R :=
  fun j => r j.castSucc

/-- Multiply adjacent entries and retain their source order. -/
def hochschildMulAdjacent [Mul R] {n : ℕ} (i : Fin n) (r : Fin (n + 1) → R) : Fin n → R :=
  fun j => if j = i then r i.castSucc * r i.succ else r (i.succ.succAbove j)

/-- Insert the unit in the selected position of a tensor tuple. -/
def hochschildInsertOne [One R] {n : ℕ} (i : Fin (n + 1)) (r : Fin n → R) : Fin (n + 1) → R :=
  Fin.insertNth i 1 r

/-- The left action `r ⊗ₜ m ↦ r • m` on a bimodule `M`, as a morphism of
`Rᵐᵒᵖ`-modules `tensorObj k R M ⟶ M`. -/
@[nolint unusedArguments] -- Deleting it would orphan it in `bimoduleAction_tmul` and wrappers.
noncomputable def bimoduleAction (k : Type u) (R : Type v) (M : Type (max u v w))
    [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] :
    tensorObj k R (ModuleCat.of Rᵐᵒᵖ M) ⟶ ModuleCat.of Rᵐᵒᵖ M := by
  let X := ModuleCat.of Rᵐᵒᵖ M
  letI : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightSMul k R X
  letI : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
    tensorRightModule k R X
  let action : R ⊗[k] (underlying k R X).carrier →ₗ[k] M :=
    TensorProduct.lift
      (LinearMap.mk₂ k
        (fun (r : R) (m : (underlying k R X).carrier) =>
          r • (show M from m))
        (by
          intro r₁ r₂ m
          exact add_smul r₁ r₂ (show M from m))
        (by
          intro c r m
          exact smul_assoc c r (show M from m))
        (by
          intro r m₁ m₂
          exact smul_add r (show M from m₁) (show M from m₂))
        (by
          intro c r m
          have hc :
              (show M from
                @SMul.smul k (underlying k R X).carrier
                  (underlying k R
                      X).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                  c m) = c • (show M from m) := by
            change (MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) •
                (show M from m) = c • (show M from m)
            exact IsScalarTower.algebraMap_smul Rᵐᵒᵖ c (show M from m)
          change r • (show M from
              @SMul.smul k (underlying k R X).carrier
                (underlying k R X).isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
                c m) = c • (r • (show M from m))
          calc
            _ = r • (c • (show M from m)) :=
              congrArg (fun q : M => r • q) hc
            _ = _ := (smul_comm c r (show M from m)).symm))
  change ModuleCat.of Rᵐᵒᵖ
      (R ⊗[k] (underlying k R X).carrier) ⟶ X
  exact ModuleCat.ofHom
    { toFun := action
      map_add' := action.map_add
      map_smul' := by
        intro s z
        change action
            (@SMul.smul Rᵐᵒᵖ
              (R ⊗[k] (underlying k R X).carrier)
              (tensorRightSMul k R X) s z) =
          s • action z
        induction z using TensorProduct.inductionOn with
        | tmul r m =>
            rw [tensorRightModule_smul_tmul]
            change r • (s • (show M from m)) =
              s • (r • (show M from m))
            exact smul_comm r s (show M from m)
        | add x y hx hy =>
            rw [tensorRightSMul_smul_add, action.map_add, hx, hy,
              action.map_add, smul_add] }

@[simp]
theorem bimoduleAction_tmul (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (r : R) (m : M) :
    (bimoduleAction k R M).hom (r ⊗ₜ[k] m) = r • m := by
  rfl

/-- The left action makes a bimodule into an algebra for the lifted
tensor monad. -/
noncomputable def bimoduleAlgebra (k : Type u) (R : Type v) (M : Type (max u v w))
    [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] : (tensorMonad k R).Algebra where
  A := ModuleCat.of Rᵐᵒᵖ M
  a := bimoduleAction k R M
  unit := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (1 : R) • (show M from m) = m
    exact one_smul R (show M from m)
  assoc := by
    let X := ModuleCat.of Rᵐᵒᵖ M
    let TX := tensorObj k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightSMul k R X
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R X).carrier) :=
      tensorRightModule k R X
    let : SMul Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightSMul k R TX
    let : Module Rᵐᵒᵖ (R ⊗[k] (underlying k R TX).carrier) :=
      tensorRightModule k R TX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (bimoduleAction k R M).hom ((tensorMul k R X).hom z) =
      (bimoduleAction k R M).hom
        ((tensorMap k R (bimoduleAction k R M)).hom z)
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
        refine tensorUnderlying_induction k R X (fun y =>
          (bimoduleAction k R M).hom
              ((tensorMul k R X).hom (r ⊗ₜ[k] y)) =
            (bimoduleAction k R M).hom
              ((tensorMap k R (bimoduleAction k R M)).hom
                (r ⊗ₜ[k] y))) ?_ ?_ y
        · intro s m
          let mM : M := show M from m
          let sx : (underlying k R TX).carrier :=
            (tensorUnderlyingIso k R X).inv.hom
              (s ⊗ₜ[k] (show (underlying k R X).carrier from mM))
          let zX : (tensorObj k R TX).carrier := r ⊗ₜ[k] sx
          change (bimoduleAction k R M).hom
              ((tensorMul k R X).hom zX) =
            (bimoduleAction k R M).hom
              ((tensorMap k R (bimoduleAction k R M)).hom zX)
          calc
            (bimoduleAction k R M).hom ((tensorMul k R X).hom zX) =
              (bimoduleAction k R M).hom ((r * s) ⊗ₜ[k] mM) :=
                congrArg (bimoduleAction k R M).hom
                  (tensorMul_tmul_via_underlyingIso k R X r s mM)
            _ = (r * s) • mM := bimoduleAction_tmul k R M (r * s) mM
            _ = r • (s • mM) := mul_smul r s mM
            _ = (bimoduleAction k R M).hom (r ⊗ₜ[k] (s • mM)) :=
              (bimoduleAction_tmul k R M r (s • mM)).symm
            _ = (bimoduleAction k R M).hom
                (r ⊗ₜ[k] (bimoduleAction k R M).hom
                  (show TX.carrier from sx)) :=
              congrArg (fun q : M =>
                (bimoduleAction k R M).hom (r ⊗ₜ[k] q))
                  (bimoduleAction_tmul k R M s mM).symm
            _ = (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom zX) :=
              congrArg (bimoduleAction k R M).hom
                (tensorMap_tmul k R (bimoduleAction k R M) r
                  (show TX.carrier from sx)).symm
        · intro x y hx hy
          rw [TensorProduct.tmul_add]
          calc
            (bimoduleAction k R M).hom
                ((tensorMul k R X).hom
                  ((r ⊗ₜ[k] x) + (r ⊗ₜ[k] y))) =
              (bimoduleAction k R M).hom
                ((tensorMul k R X).hom (r ⊗ₜ[k] x) +
                  (tensorMul k R X).hom (r ⊗ₜ[k] y)) :=
                    congrArg (bimoduleAction k R M).hom
                      ((tensorMul k R X).hom.map_add _ _)
            _ = (bimoduleAction k R M).hom
                  ((tensorMul k R X).hom (r ⊗ₜ[k] x)) +
                (bimoduleAction k R M).hom
                  ((tensorMul k R X).hom (r ⊗ₜ[k] y)) :=
              (bimoduleAction k R M).hom.map_add _ _
            _ = (bimoduleAction k R M).hom
                  ((tensorMap k R (bimoduleAction k R M)).hom
                    (r ⊗ₜ[k] x)) +
                (bimoduleAction k R M).hom
                  ((tensorMap k R (bimoduleAction k R M)).hom
                    (r ⊗ₜ[k] y)) := congrArg₂ (· + ·) hx hy
            _ = (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom
                    (r ⊗ₜ[k] x) +
                  (tensorMap k R (bimoduleAction k R M)).hom
                    (r ⊗ₜ[k] y)) :=
              ((bimoduleAction k R M).hom.map_add _ _).symm
            _ = (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom
                  ((r ⊗ₜ[k] x) + (r ⊗ₜ[k] y))) :=
              congrArg (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom.map_add _ _).symm
    | add x y hx hy =>
        calc
          (bimoduleAction k R M).hom ((tensorMul k R X).hom (x + y)) =
            (bimoduleAction k R M).hom
              ((tensorMul k R X).hom x + (tensorMul k R X).hom y) :=
                congrArg (bimoduleAction k R M).hom
                  ((tensorMul k R X).hom.map_add x y)
          _ = (bimoduleAction k R M).hom ((tensorMul k R X).hom x) +
              (bimoduleAction k R M).hom ((tensorMul k R X).hom y) :=
            (bimoduleAction k R M).hom.map_add _ _
          _ = (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom x) +
              (bimoduleAction k R M).hom
                ((tensorMap k R (bimoduleAction k R M)).hom y) :=
            congrArg₂ (· + ·) hx hy
          _ = (bimoduleAction k R M).hom
              ((tensorMap k R (bimoduleAction k R M)).hom x +
                (tensorMap k R (bimoduleAction k R M)).hom y) :=
            ((bimoduleAction k R M).hom.map_add _ _).symm
          _ = (bimoduleAction k R M).hom
              ((tensorMap k R (bimoduleAction k R M)).hom (x + y)) :=
            congrArg (bimoduleAction k R M).hom
              ((tensorMap k R (bimoduleAction k R M)).hom.map_add x y).symm

@[simp]
theorem bimoduleAlgebra_a_tmul (k : Type u) (R : Type v) (M : Type (max u v w))
    [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (r : R) (m : M) :
    (bimoduleAlgebra k R M).a.hom (r ⊗ₜ[k] m) = r • m :=
  by
    exact bimoduleAction_tmul k R M r m

/-- The native `k`-linear Hochschild bar. -/
noncomputable def barK (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [Module k M]
    [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] : SimplicialObject (ModuleCat.{max u v w} k) :=
  Monad.algebraBar (forgetRightModule k R) (bimoduleAlgebra k R M)

/-- The canonical additive Hochschild bar. -/
noncomputable def bar (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [Module k M]
    [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] : SimplicialObject (ModuleCat.{max u v w} ℤ) :=
  barK k R M ⋙ ModuleCat.restrictScalars (Int.castRingHom k)

/-- `PUnit ⊕ Fin n` indexes a new first tensor factor followed by the old
`n` factors. -/
def finSuccSumEquiv (n : ℕ) : PUnit.{1} ⊕ Fin n ≃ Fin (n + 1) :=
  TensorPower.consIndexEquiv n

@[simp]
theorem finSuccSumEquiv_inl (n : ℕ) (x : PUnit.{1}) :
    finSuccSumEquiv n (Sum.inl x) = 0 :=
  TensorPower.consIndexEquiv_inl n x

@[simp]
theorem finSuccSumEquiv_inr (n : ℕ) (i : Fin n) :
    finSuccSumEquiv n (Sum.inr i) = i.succ :=
  TensorPower.consIndexEquiv_inr n i

/-- The empty tensor power is the scalar ring. -/
noncomputable def tensorPowerZeroEquiv (k : Type u) (R : Type v) [CommRing k]
    [AddCommGroup R] [Module k R] : TensorPower k 0 R ≃ₗ[k] k :=
  TensorPower.zeroEquiv k R

/-- Split a tensor power at its first coordinate. -/
noncomputable def tensorPowerConsEquiv (k : Type u) (R : Type v) [CommRing k]
    [AddCommGroup R] [Module k R] (n : ℕ) :
    R ⊗[k] TensorPower k n R ≃ₗ[k] TensorPower k (n + 1) R :=
  TensorPower.consEquiv k R n

@[simp]
theorem tensorPowerConsEquiv_tmul (k : Type u) (R : Type v) [CommRing k]
    [AddCommGroup R] [Module k R] (n : ℕ) (r : R) (s : Fin n → R) :
    tensorPowerConsEquiv k R n (r ⊗ₜ[k] PiTensorProduct.tprod k s) =
      PiTensorProduct.tprod k (Fin.cons r s) :=
  TensorPower.consEquiv_tmul k R n r s

/-- The canonical restricted `k`-module on a right module agrees with the
specified coefficient `k`-module. -/
noncomputable def coefficientUnderlyingIso (k : Type u) (R : Type v) (M : Type (max u v w))
    [CommRing k]
    [Ring R] [Algebra k R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module k M] [IsScalarTower k Rᵐᵒᵖ M] :
    underlying k R (ModuleCat.of Rᵐᵒᵖ M) ≅ ModuleCat.of k M :=
  by
    let A := underlying k R (ModuleCat.of Rᵐᵒᵖ M)
    let B := ModuleCat.of k M
    let hom : A ⟶ B := ConcreteCategory.ofHom
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c m
          change @SMul.smul k A.carrier
              A.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
              c m =
            @SMul.smul k B.carrier
              B.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
              c (show B.carrier from m)
          change (MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) •
              (show M from m) = c • (show M from m)
          exact IsScalarTower.algebraMap_smul Rᵐᵒᵖ c (show M from m) }
    let inv : B ⟶ A := ConcreteCategory.ofHom
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c m
          change @SMul.smul k B.carrier
              B.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
              c m =
            @SMul.smul k A.carrier
              A.isModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
              c (show A.carrier from m)
          change c • (show M from m) =
            (MulOpposite.op (algebraMap k R c) : Rᵐᵒᵖ) •
              (show M from m)
          exact (IsScalarTower.algebraMap_smul Rᵐᵒᵖ c
            (show M from m)).symm }
    exact
      { hom := hom
        inv := inv
        hom_inv_id := by apply ModuleCat.hom_ext; rfl
        inv_hom_id := by apply ModuleCat.hom_ext; rfl }

/-- Native iterated tensors, written as an outer-to-inner tuple. -/
noncomputable def rawPure (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    (n : ℕ) → (Fin n → R) → X.carrier →
      ((Monad.monadPow (tensorMonad k R) n).obj X).carrier
  | 0, _, x => x
  | n + 1, r, x =>
      (eqToHom (Monad.monadPow_succ_obj_eq (tensorMonad k R) n X).symm).hom
        (r 0 ⊗ₜ[k] rawPure k R X n (fun i => r i.succ) x)

@[simp]
private theorem eqToHom_inv_apply [Ring R]
    {X Y : ModuleCat.{w} Rᵐᵒᵖ} (h : X = Y) (y : Y.carrier) :
    (eqToHom h).hom ((eqToHom h.symm).hom y) = y := by
  cases h
  rfl

private theorem forgetRight_map_eqToHom_inv_apply
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (h : X = Y) (y : Y.carrier) :
    ((forgetRight k R).map (eqToHom h)).hom
        ((eqToHom h.symm).hom y) = y := by
  cases h
  rfl

private theorem monadPow_map_rawPure
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    {X Y : ModuleCat.{max u v w} Rᵐᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (r : Fin n → R) (x : X.carrier) :
    ((Monad.monadPow (tensorMonad k R) n).map f).hom
        (rawPure k R X n r x) =
      rawPure k R Y n r (f.hom x) := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
      let Xn := (Monad.monadPow (tensorMonad k R) n).obj X
      let Yn := (Monad.monadPow (tensorMonad k R) n).obj Y
      let px : Xn.carrier :=
        rawPure k R X n (fun i => r i.succ) x
      let py : Yn.carrier :=
        rawPure k R Y n (fun i => r i.succ) (f.hom x)
      let tx : ((tensorMonad k R).obj Xn).carrier := show _ from
        r 0 ⊗ₜ[k] (show (underlying k R Xn).carrier from px)
      let ty : ((tensorMonad k R).obj Yn).carrier := show _ from
        r 0 ⊗ₜ[k] (show (underlying k R Yn).carrier from py)
      let hX := Monad.monadPow_succ_obj_eq (tensorMonad k R) n X
      let hY := Monad.monadPow_succ_obj_eq (tensorMonad k R) n Y
      have hrawX :
          rawPure k R X (n + 1) r x =
            (eqToHom hX.symm).hom tx :=
        rfl
      have hrawY :
          rawPure k R Y (n + 1) r (f.hom x) =
            (eqToHom hY.symm).hom ty :=
        rfl
      have hnat := ConcreteCategory.congr_hom
        (Monad.monadPow_succ_obj_eq_naturality
          (tensorMonad k R) n f)
        (rawPure k R X (n + 1) r x)
      change (eqToHom hY).hom
        (((Monad.monadPow (tensorMonad k R) (n + 1)).map f).hom
          (rawPure k R X (n + 1) r x)) =
        (tensorMap k R
          ((Monad.monadPow (tensorMonad k R) n).map f)).hom
            ((eqToHom hX).hom
              (rawPure k R X (n + 1) r x)) at hnat
      rw [hrawX] at hnat
      have hcancelX :
          (eqToHom hX).hom ((eqToHom hX.symm).hom tx) = tx :=
        eqToHom_inv_apply hX tx
      change (eqToHom hY).hom
          (((Monad.monadPow (tensorMonad k R) (n + 1)).map f).hom
            ((eqToHom hX.symm).hom tx)) =
        (tensorMap k R
          ((Monad.monadPow (tensorMonad k R) n).map f)).hom
            ((eqToHom hX).hom ((eqToHom hX.symm).hom tx)) at hnat
      rw [hcancelX] at hnat
      have hmap :
          (tensorMap k R
            ((Monad.monadPow (tensorMonad k R) n).map f)).hom
              (show (tensorObj k R Xn).carrier from tx) =
            (show (tensorObj k R Yn).carrier from ty) := by
        rw [tensorMap_tmul, ih]
      rw [hmap] at hnat
      calc
        _ = (eqToHom hY.symm).hom
            ((eqToHom hY).hom
              (((Monad.monadPow (tensorMonad k R) (n + 1)).map f).hom
                (rawPure k R X (n + 1) r x))) :=
          (eqToHom_inv_apply hY.symm _).symm
        _ = (eqToHom hY.symm).hom ty :=
          congrArg (eqToHom hY.symm).hom hnat
        _ = _ := hrawY.symm

private theorem rawPure_snoc
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ)
    (r : Fin (n + 1) → R) (x : X.carrier) :
    rawPure k R (tensorObj k R X) n (Fin.init r)
        (show (tensorObj k R X).carrier from
          r (Fin.last n) ⊗ₜ[k]
            (show (underlying k R X).carrier from x)) =
      rawPure k R X (n + 1) r x := by
  induction n generalizing X with
  | zero =>
      rfl
  | succ n ih =>
      simp only [rawPure]
      have hcoords :
          (fun i : Fin n => Fin.init r i.succ) =
            Fin.init (Fin.tail r) := by
        funext i
        rfl
      have hlast :
          r (Fin.last (n + 1)) = Fin.tail r (Fin.last n) := by
        rfl
      rw [hcoords, hlast, ih (X := X) (r := Fin.tail r)]
      rfl

private def rawMuPos (n : ℕ) (j : Fin n) : Fin n :=
  ⟨n - 1 - j.val, by have := j.isLt; omega⟩

private def rawEtaPos (n : ℕ) (j : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - j.val, by have := j.isLt; omega⟩

private theorem rawMuPos_rev (n : ℕ) (i : Fin n) :
    rawMuPos n i.rev = i := by
  apply Fin.ext
  simp only [rawMuPos, Fin.val_rev]
  have := i.isLt
  omega

private theorem rawEtaPos_rev (n : ℕ) (i : Fin (n + 1)) :
    rawEtaPos n i.rev = i := by
  apply Fin.ext
  simp only [rawEtaPos, Fin.val_rev]
  have := i.isLt
  omega

private theorem rawMuPos_succ_zero (n : ℕ) :
    rawMuPos (n + 1) (0 : Fin (n + 1)) = Fin.last n := by
  apply Fin.ext
  simp [rawMuPos]

private theorem rawMuPos_succ_succ (n : ℕ) (j : Fin n) :
    rawMuPos (n + 1) j.succ = (rawMuPos n j).castSucc := by
  apply Fin.ext
  simp only [rawMuPos, Fin.val_succ, Fin.val_castSucc]
  have := j.isLt
  omega

private theorem rawEtaPos_succ_zero (n : ℕ) :
    rawEtaPos (n + 1) (0 : Fin (n + 2)) = Fin.last (n + 1) := by
  apply Fin.ext
  simp [rawEtaPos]

private theorem rawEtaPos_succ_succ (n : ℕ) (j : Fin (n + 1)) :
    rawEtaPos (n + 1) j.succ = (rawEtaPos n j).castSucc := by
  apply Fin.ext
  simp only [rawEtaPos, Fin.val_succ, Fin.val_castSucc]
  have := j.isLt
  omega

/-- Merging the final adjacent pair retains the preceding tuple and its ordered product. -/
theorem hochschildMulAdjacent_last_snoc
    {R : Type u} [Mul R] (n : ℕ) (r : Fin (n + 2) → R) :
    hochschildMulAdjacent (Fin.last n) r =
      Fin.snoc (Fin.init (Fin.init r))
        (r (Fin.last n).castSucc * r (Fin.last n).succ) := by
  funext q
  refine Fin.lastCases ?_ (fun q => ?_) q
  · simp [hochschildMulAdjacent]
  · rw [Fin.snoc_castSucc]
    unfold hochschildMulAdjacent
    have hne : q.castSucc ≠ Fin.last n :=
      Fin.ne_of_lt q.castSucc_lt_last
    rw [ite_eq_right hne]
    have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hlast, Fin.succAbove_last]
    rfl

/-- Merging before the final factor commutes with retaining that final factor. -/
theorem hochschildMulAdjacent_castSucc_snoc
    {R : Type u} [Mul R] (n : ℕ) (p : Fin n)
    (r : Fin (n + 2) → R) :
    hochschildMulAdjacent p.castSucc r =
      Fin.snoc (hochschildMulAdjacent p (Fin.init r))
        (r (Fin.last (n + 1))) := by
  funext q
  refine Fin.lastCases ?_ (fun q => ?_) q
  · rw [Fin.snoc_last]
    unfold hochschildMulAdjacent
    have hne : Fin.last n ≠ p.castSucc :=
      Fin.ne_of_gt p.castSucc_lt_last
    rw [ite_eq_right hne]
    have hle : (p.castSucc).succ ≤ (Fin.last n).castSucc := by
      rw [Fin.succ_le_castSucc_iff]
      exact p.castSucc_lt_last
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    rfl
  · rw [Fin.snoc_castSucc]
    unfold hochschildMulAdjacent
    by_cases hqp : q = p
    · subst q
      rw [ite_eq_left rfl, ite_eq_left rfl]
      change r p.castSucc.castSucc * r p.castSucc.succ =
        r p.castSucc.castSucc * r p.succ.castSucc
      rw [Fin.succ_castSucc]
    · have hcast : q.castSucc ≠ p.castSucc := by
        intro h
        exact hqp ((Fin.castSucc_injective n) h)
      rw [ite_eq_right hcast, ite_eq_right hqp]
      have hpivot : (p.castSucc).succ = p.succ.castSucc := rfl
      rw [hpivot, Fin.castSucc_succAbove_castSucc]
      rfl

private theorem hochschildInsertOne_last_snoc
    {R : Type u} [Ring R] (n : ℕ) (r : Fin (n + 1) → R) :
    hochschildInsertOne (Fin.last (n + 1)) r = Fin.snoc r 1 := by
  simpa only [hochschildInsertOne] using
    (Fin.insertNth_last' (n := n + 1) (x := (1 : R)) (p := r))

private theorem hochschildInsertOne_castSucc_snoc
    {R : Type u} [Ring R] (n : ℕ) (p : Fin (n + 1))
    (r : Fin (n + 1) → R) :
    hochschildInsertOne p.castSucc r =
      Fin.snoc (hochschildInsertOne p (Fin.init r)) (r (Fin.last n)) := by
  funext q
  cases q using Fin.succAboveCases p.castSucc with
  | x =>
      simp only [hochschildInsertOne, Fin.insertNth_apply_same,
        Fin.snoc_castSucc]
  | p q =>
      simp only [hochschildInsertOne, Fin.insertNth_apply_succAbove]
      cases q using Fin.lastCases with
      | last =>
          have hle : p.castSucc ≤ (Fin.last n).castSucc :=
            Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last p)
          have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
          rw [Fin.succAbove_of_le_castSucc _ _ hle, hlast,
            Fin.snoc_last]
      | cast q =>
          rw [Fin.castSucc_succAbove_castSucc,
            Fin.snoc_castSucc, Fin.insertNth_apply_succAbove]
          rfl

private theorem muAtPos_rawPure_left
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ) (j : Fin n)
    (r : Fin (n + 1) → R) (x : X.carrier) :
    (Monad.muAtPos (tensorMonad k R) n j X).hom
        (rawPure k R X (n + 1) r x) =
      rawPure k R X n (hochschildMulAdjacent (rawMuPos n j) r) x := by
  induction n generalizing X with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      match j with
      | ⟨0, hj⟩ =>
          let TX := tensorObj k R X
          let t : R := r (Fin.last n).succ
          let s : R := r (Fin.last n).castSucc
          let xt : TX.carrier := show TX.carrier from
            t ⊗ₜ[k] (show (underlying k R X).carrier from x)
          let zst : (tensorObj k R TX).carrier := show _ from
            s ⊗ₜ[k] (show (underlying k R TX).carrier from xt)
          let stx : TX.carrier := show TX.carrier from
            (s * t) ⊗ₜ[k] (show (underlying k R X).carrier from x)
          have hindex : (⟨0, hj⟩ : Fin (n + 1)) = 0 := by
            apply Fin.ext
            rfl
          have hpos :
              rawMuPos (n + 1) (⟨0, hj⟩ : Fin (n + 1)) =
                Fin.last n := by
            rw [hindex]
            exact rawMuPos_succ_zero n
          have hxt :
              (show (underlying k R TX).carrier from xt) =
                (tensorUnderlyingIso k R X).inv.hom
                  (t ⊗ₜ[k]
                    (show (underlying k R X).carrier from x)) := by
            change t ⊗ₜ[k] (show (underlying k R X).carrier from x) =
              (tensorUnderlyingIso k R X).inv.hom
                (t ⊗ₜ[k]
                  (show (underlying k R X).carrier from x))
            rw [tensorUnderlyingIso_inv_apply]
          have hmul :
              (tensorMul k R X).hom zst = stx := by
            change (tensorMul k R X).hom
                (s ⊗ₜ[k] (show (underlying k R TX).carrier from xt)) =
              (s * t) ⊗ₜ[k] x
            rw [hxt]
            exact tensorMul_tmul_via_underlyingIso k R X s t x
          change ((Monad.monadPow (tensorMonad k R) n).map
            (tensorMul k R X)).hom
              (rawPure k R X (n + 2) r x) = _
          rw [← rawPure_snoc k R X (n + 1) r x]
          change ((Monad.monadPow (tensorMonad k R) n).map
            (tensorMul k R X)).hom
              (rawPure k R TX (n + 1) (Fin.init r) xt) = _
          rw [← rawPure_snoc k R TX n (Fin.init r) xt]
          rw [monadPow_map_rawPure]
          have hzst :
              (show (tensorObj k R TX).carrier from
                Fin.init r (Fin.last n) ⊗ₜ[k]
                  (show (underlying k R TX).carrier from xt)) = zst := by
            dsimp only [zst, s]
            rfl
          rw [hzst, hmul,
            hpos,
            hochschildMulAdjacent_last_snoc]
          rw [← rawPure_snoc k R X n
            (Fin.snoc (Fin.init (Fin.init r)) (s * t)) x]
          dsimp only [s, t, stx]
          simp only [Fin.init_snoc, Fin.snoc_last]
      | ⟨q + 1, hj⟩ =>
          let q0 : Fin n := ⟨q, by omega⟩
          let TX := tensorObj k R X
          let t : R := r (Fin.last (n + 1))
          let xt : TX.carrier := show TX.carrier from
            t ⊗ₜ[k] (show (underlying k R X).carrier from x)
          have hpos :
              rawMuPos (n + 1) (⟨q + 1, hj⟩ : Fin (n + 1)) =
                (rawMuPos n q0).castSucc :=
            rawMuPos_succ_succ n q0
          change (Monad.muAtPos (tensorMonad k R) n q0 TX).hom
              (rawPure k R X (n + 2) r x) = _
          rw [← rawPure_snoc k R X (n + 1) r x]
          rw [ih (X := TX) (j := q0) (r := Fin.init r) (x := xt)]
          rw [hpos, hochschildMulAdjacent_castSucc_snoc]
          rw [← rawPure_snoc k R X n
            (Fin.snoc
              (hochschildMulAdjacent (rawMuPos n q0) (Fin.init r)) t) x]
          dsimp only [TX, xt, t]
          simp only [Fin.init_snoc, Fin.snoc_last]

private theorem etaAtPos_rawPure_left
    (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]
    (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ) (j : Fin (n + 1))
    (r : Fin n → R) (x : X.carrier) :
    (Monad.etaAtPos (tensorMonad k R) n j X).hom
        (rawPure k R X n r x) =
      rawPure k R X (n + 1) (hochschildInsertOne (rawEtaPos n j) r) x := by
  induction n generalizing X with
  | zero =>
      have hj : j = (0 : Fin 1) := by
        apply Fin.ext
        omega
      subst j
      change (tensorUnit k R X).hom x =
        (eqToHom (Monad.monadPow_succ_obj_eq
          (tensorMonad k R) 0 X).symm).hom
            ((1 : R) ⊗ₜ[k]
              (show (underlying k R X).carrier from x))
      rw [tensorUnit_apply]
      rfl
  | succ n ih =>
      match j with
      | ⟨0, hj⟩ =>
          let TX := tensorObj k R X
          let oneX : TX.carrier := show TX.carrier from
            (1 : R) ⊗ₜ[k]
              (show (underlying k R X).carrier from x)
          have hunit : (tensorUnit k R X).hom x = oneX := by
            exact tensorUnit_apply k R X x
          have hindex : (⟨0, hj⟩ : Fin (n + 2)) = 0 := by
            apply Fin.ext
            rfl
          have hpos :
              rawEtaPos (n + 1) (⟨0, hj⟩ : Fin (n + 2)) =
                Fin.last (n + 1) := by
            rw [hindex]
            exact rawEtaPos_succ_zero n
          change ((Monad.monadPow (tensorMonad k R) (n + 1)).map
            (tensorUnit k R X)).hom
              (rawPure k R X (n + 1) r x) = _
          rw [monadPow_map_rawPure, hunit, hpos,
            hochschildInsertOne_last_snoc]
          rw [← rawPure_snoc k R X (n + 1) (Fin.snoc r 1) x]
          dsimp only [TX, oneX]
          simp only [Fin.init_snoc, Fin.snoc_last]
      | ⟨q + 1, hj⟩ =>
          let q0 : Fin (n + 1) := ⟨q, by omega⟩
          let TX := tensorObj k R X
          let t : R := r (Fin.last n)
          let xt : TX.carrier := show TX.carrier from
            t ⊗ₜ[k] (show (underlying k R X).carrier from x)
          have hpos :
              rawEtaPos (n + 1) (⟨q + 1, hj⟩ : Fin (n + 2)) =
                (rawEtaPos n q0).castSucc :=
            rawEtaPos_succ_succ n q0
          change (Monad.etaAtPos (tensorMonad k R) n q0 TX).hom
              (rawPure k R X (n + 1) r x) = _
          rw [← rawPure_snoc k R X n r x]
          rw [ih (X := TX) (j := q0) (r := Fin.init r) (x := xt)]
          rw [hpos, hochschildInsertOne_castSucc_snoc]
          rw [← rawPure_snoc k R X (n + 1)
            (Fin.snoc
              (hochschildInsertOne (rawEtaPos n q0) (Fin.init r)) t) x]
          dsimp only [TX, xt, t]
          simp only [Fin.init_snoc, Fin.snoc_last]

/-- Move the right-module carrier to the front of the iterated tensor monad,
preserving the outer-to-inner order of all `R` factors. -/
noncomputable def coordinateIso (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) :
    ∀ n : ℕ,
      (forgetRight k R).obj ((Monad.monadPow (tensorMonad k R) n).obj X) ≅
        ModuleCat.of k
          ((underlying k R X).carrier ⊗[k] TensorPower k n R)
  | 0 => LinearEquiv.toModuleIso
      ((TensorProduct.rid k (underlying k R X).carrier).symm.trans
        (TensorProduct.congr (LinearEquiv.refl k _)
          (tensorPowerZeroEquiv k R).symm))
  | n + 1 =>
      (forgetRight k R).mapIso
          (eqToIso (Monad.monadPow_succ_obj_eq (tensorMonad k R) n X)) ≪≫
        tensorUnderlyingIso k R
          ((Monad.monadPow (tensorMonad k R) n).obj X) ≪≫
        LinearEquiv.toModuleIso
          ((TensorProduct.congr (LinearEquiv.refl k R)
              (coordinateIso k R X n).toLinearEquiv).trans
            ((TensorProduct.assoc k R (underlying k R X).carrier
                (TensorPower k n R)).symm.trans
              ((TensorProduct.congr
                  (TensorProduct.comm k R (underlying k R X).carrier)
                  (LinearEquiv.refl k (TensorPower k n R))).trans
                ((TensorProduct.assoc k (underlying k R X).carrier R
                    (TensorPower k n R)).trans
                  ((tensorPowerConsEquiv k R n).lTensor
                    (underlying k R X).carrier)))))

@[simp]
theorem coordinateIso_hom_rawPure (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ)
    (r : Fin n → R) (x : X.carrier) :
    (coordinateIso k R X n).hom.hom (rawPure k R X n r x) =
      x ⊗ₜ[k] PiTensorProduct.tprod k r := by
  induction n generalizing X with
  | zero =>
      simp only [coordinateIso, rawPure]
      apply congrArg (fun q => x ⊗ₜ[k] q)
      apply (tensorPowerZeroEquiv k R).injective
      simp [tensorPowerZeroEquiv, TensorPower.zeroEquiv,
        PiTensorProduct.isEmptyEquiv_apply_tprod]
  | succ n ih =>
      let Xn := (Monad.monadPow (tensorMonad k R) n).obj X
      let px : Xn.carrier :=
        rawPure k R X n (fun i => r i.succ) x
      let ux : (underlying k R Xn).carrier :=
        show (underlying k R Xn).carrier from px
      let zx : (underlying k R (tensorObj k R Xn)).carrier :=
        show (underlying k R (tensorObj k R Xn)).carrier from
          r 0 ⊗ₜ[k] ux
      let e :
          (R ⊗[k] (underlying k R Xn).carrier) ≃ₗ[k]
            ((underlying k R X).carrier ⊗[k] TensorPower k (n + 1) R) :=
        (TensorProduct.congr (LinearEquiv.refl k R)
              (coordinateIso k R X n).toLinearEquiv).trans
          ((TensorProduct.assoc k R (underlying k R X).carrier
                (TensorPower k n R)).symm.trans
            ((TensorProduct.congr
                  (TensorProduct.comm k R (underlying k R X).carrier)
                  (LinearEquiv.refl k (TensorPower k n R))).trans
              ((TensorProduct.assoc k (underlying k R X).carrier R
                    (TensorPower k n R)).trans
                ((tensorPowerConsEquiv k R n).lTensor
                  (underlying k R X).carrier))))
      let ψ :
          ModuleCat.of k (R ⊗[k] (underlying k R Xn).carrier) ≅
            ModuleCat.of k
              ((underlying k R X).carrier ⊗[k] TensorPower k (n + 1) R) :=
        LinearEquiv.toModuleIso e
      have hih :
          (coordinateIso k R X n).toLinearEquiv ux =
            (show (underlying k R X).carrier from x) ⊗ₜ[k]
              PiTensorProduct.tprod k (fun i => r i.succ) := by
        change (coordinateIso k R X n).hom.hom
            (rawPure k R X n (fun i => r i.succ) x) = _
        exact ih X (fun i => r i.succ) x
      have hψ :
          (tensorUnderlyingIso k R Xn).hom.hom zx =
            r 0 ⊗ₜ[k] ux :=
        tensorUnderlyingIso_hom_apply k R Xn zx
      let hX : (Monad.monadPow (tensorMonad k R) (n + 1)).obj X =
          tensorObj k R Xn :=
        Monad.monadPow_succ_obj_eq (tensorMonad k R) n X
      have hcast :
          ((forgetRight k R).map (eqToHom hX)).hom
              ((eqToHom hX.symm).hom
                (show (tensorObj k R Xn).carrier from r 0 ⊗ₜ[k] ux)) = zx :=
        forgetRight_map_eqToHom_inv_apply k R hX
          (show (tensorObj k R Xn).carrier from r 0 ⊗ₜ[k] ux)
      change ψ.hom.hom
          ((tensorUnderlyingIso k R Xn).hom.hom
            (((forgetRight k R).map (eqToHom hX)).hom
              ((eqToHom hX.symm).hom
                (show (tensorObj k R Xn).carrier from r 0 ⊗ₜ[k] ux)))) =
        (show (underlying k R X).carrier from x) ⊗ₜ[k]
          PiTensorProduct.tprod k r
      calc
        _ = ψ.hom.hom ((tensorUnderlyingIso k R Xn).hom.hom zx) :=
          congrArg (fun z : (underlying k R (tensorObj k R Xn)).carrier =>
            ψ.hom.hom ((tensorUnderlyingIso k R Xn).hom.hom z)) hcast
        _ = ψ.hom.hom (r 0 ⊗ₜ[k] ux) := congrArg ψ.hom.hom hψ
        _ = (show (underlying k R X).carrier from x) ⊗ₜ[k]
            PiTensorProduct.tprod k r := by
          change e (r 0 ⊗ₜ[k] ux) =
            (show (underlying k R X).carrier from x) ⊗ₜ[k]
              PiTensorProduct.tprod k r
          dsimp only [e]
          simp only [LinearEquiv.trans_apply]
          rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
          rw [hih]
          change
            (show (underlying k R X).carrier from x) ⊗ₜ[k]
                tensorPowerConsEquiv k R n
                  (r 0 ⊗ₜ[k]
                    PiTensorProduct.tprod k (fun i => r i.succ)) =
              (show (underlying k R X).carrier from x) ⊗ₜ[k]
                PiTensorProduct.tprod k r
          rw [tensorPowerConsEquiv_tmul]
          exact congrArg
            (fun q => (show (underlying k R X).carrier from x) ⊗ₜ[k] q)
            (congrArg (PiTensorProduct.tprod k) (Fin.cons_self_tail r))

@[simp]
theorem coordinateIso_inv_tprod (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ)
    (r : Fin n → R) (x : X.carrier) :
    (coordinateIso k R X n).inv.hom
        (x ⊗ₜ[k] PiTensorProduct.tprod k r) = rawPure k R X n r x := by
  change (coordinateIso k R X n).inv.hom
      ((show (underlying k R X).carrier from x) ⊗ₜ[k]
        PiTensorProduct.tprod k r) = rawPure k R X n r x
  have hhom :
      (coordinateIso k R X n).hom.hom (rawPure k R X n r x) =
        (show (underlying k R X).carrier from x) ⊗ₜ[k]
          PiTensorProduct.tprod k r :=
    coordinateIso_hom_rawPure k R X n r x
  have hcancel :
      (coordinateIso k R X n).inv.hom
          ((coordinateIso k R X n).hom.hom
            (rawPure k R X n r x)) =
        rawPure k R X n r x :=
    ConcreteCategory.congr_hom (coordinateIso k R X n).hom_inv_id _
  exact
    (congrArg (coordinateIso k R X n).inv.hom hhom.symm).trans hcancel

/-- Degreewise identification of the native bar with the source tensor
coordinates. -/
noncomputable def barObjIso (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (n : ℕ) :
    (barK k R M).obj (Opposite.op (SimplexCategory.mk n)) ≅
      ModuleCat.of k (M ⊗[k] TensorPower k n R) :=
  eqToIso (Monad.algebraBar_obj (forgetRightModule k R)
      (bimoduleAlgebra k R M) n) ≪≫
    coordinateIso k R (ModuleCat.of Rᵐᵒᵖ M) n ≪≫
    LinearEquiv.toModuleIso
      (TensorProduct.congr (coefficientUnderlyingIso k R M).toLinearEquiv
        (LinearEquiv.refl k (TensorPower k n R)))

@[simp]
theorem barObjIso_hom_rawPure (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (n : ℕ) (r : Fin n → R) (m : M) :
    (barObjIso k R M n).hom.hom
        (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m) =
      m ⊗ₜ[k] PiTensorProduct.tprod k r := by
  simp only [barObjIso, Iso.trans_hom,
    ModuleCat.hom_comp]
  change
    (LinearEquiv.toModuleIso
      (TensorProduct.congr (coefficientUnderlyingIso k R M).toLinearEquiv
        (LinearEquiv.refl k (TensorPower k n R)))).hom.hom
        ((coordinateIso k R (ModuleCat.of Rᵐᵒᵖ M) n).hom.hom
          (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k r
  rw [coordinateIso_hom_rawPure]
  rfl

@[simp]
theorem barObjIso_inv_tprod (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (n : ℕ) (r : Fin n → R) (m : M) :
    (barObjIso k R M n).inv.hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k r) =
      rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m := by
  have hhom :
      (barObjIso k R M n).hom.hom
          (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m) =
        m ⊗ₜ[k] PiTensorProduct.tprod k r :=
    barObjIso_hom_rawPure k R M n r m
  have hcancel :
      (barObjIso k R M n).inv.hom
          ((barObjIso k R M n).hom.hom
            (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m)) =
        rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m :=
    ConcreteCategory.congr_hom (barObjIso k R M n).hom_inv_id _
  exact (congrArg (barObjIso k R M n).inv.hom hhom.symm).trans hcancel

@[simp]
theorem rightActionPow_rawPure (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ)
    (r : Fin (n + 1) → R) (x : X.carrier) :
    (Monad.rightActionPow (tensorMonad k R) (forgetRightModule k R) n X).hom
        (rawPure k R X (n + 1) r x) =
      rawPure k R X n (hochschildDropFirst r)
        ((MulOpposite.op (r 0) : Rᵐᵒᵖ) • x) := by
  induction n generalizing X with
  | zero =>
      change (forgetAction k R X).hom (r 0 ⊗ₜ[k] x) =
        (MulOpposite.op (r 0) : Rᵐᵒᵖ) • x
      exact forgetAction_tmul k R X (r 0) x
  | succ n ih =>
      change
        (Monad.rightActionPow (tensorMonad k R)
          (forgetRightModule k R) n (tensorObj k R X)).hom
            (rawPure k R X (n + 2) r x) = _
      rw [← rawPure_snoc k R X (n + 1) r x]
      rw [ih (X := tensorObj k R X) (r := Fin.init r)
        (x := (show (tensorObj k R X).carrier from
          r (Fin.last (n + 1)) ⊗ₜ[k]
            (show (underlying k R X).carrier from x)))]
      rw [← rawPure_snoc k R X n (hochschildDropFirst r)
        ((MulOpposite.op (r 0) : Rᵐᵒᵖ) • x)]
      congr 2

@[simp]
theorem algebraAction_rawPure (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M]
    [IsScalarTower k Rᵐᵒᵖ M] (n : ℕ) (r : Fin (n + 1) → R) (m : M) :
    ((forgetRight k R).map
      ((Monad.monadPow (tensorMonad k R) n).map
        (bimoduleAlgebra k R M).a)).hom
        (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) (n + 1) r m) =
      rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n
        (hochschildDropLast r) (r (Fin.last n) • m) := by
  let X := ModuleCat.of Rᵐᵒᵖ M
  let mX : X.carrier := m
  let z : (tensorObj k R X).carrier :=
    r (Fin.last n) ⊗ₜ[k]
      (show (underlying k R X).carrier from mX)
  change ((Monad.monadPow (tensorMonad k R) n).map
      (bimoduleAction k R M)).hom
        (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) (n + 1) r m) = _
  have hsnoc :
      rawPure k R X (n + 1) r mX =
        rawPure k R (tensorObj k R X) n (Fin.init r) z :=
    (rawPure_snoc k R X n r mX).symm
  rw [hsnoc]
  rw [monadPow_map_rawPure, bimoduleAction_tmul]
  rfl

theorem barMuAtPos_rawPure (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ) (i : Fin n)
    (r : Fin (n + 1) → R) (x : X.carrier) :
    ((forgetRight k R).map
      (Monad.barMuAtPos (tensorMonad k R) n i X)).hom
        (rawPure k R X (n + 1) r x) =
      rawPure k R X n (hochschildMulAdjacent i r) x := by
  change (Monad.barMuAtPos (tensorMonad k R) n i X).hom
      (rawPure k R X (n + 1) r x) = _
  rw [Monad.barMuAtPos_rev]
  have h := muAtPos_rawPure_left k R X n i.rev r x
  rw [rawMuPos_rev n i] at h
  exact h

theorem barEtaAtPos_rawPure (k : Type u) (R : Type v) [CommRing k] [Ring R]
    [Algebra k R] (X : ModuleCat.{max u v w} Rᵐᵒᵖ) (n : ℕ) (i : Fin (n + 1))
    (r : Fin n → R) (x : X.carrier) :
    ((forgetRight k R).map
      (Monad.barEtaAtPos (tensorMonad k R) n i X)).hom
        (rawPure k R X n r x) =
      rawPure k R X (n + 1) (hochschildInsertOne i r) x := by
  change (Monad.barEtaAtPos (tensorMonad k R) n i X).hom
      (rawPure k R X n r x) = _
  rw [Monad.barEtaAtPos_rev]
  have h := etaAtPos_rawPure_left k R X n i.rev r x
  rw [rawEtaPos_rev n i] at h
  exact h


/-- The first face is the right coefficient action in tensor coordinates. -/
theorem bar_face_first (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
    (n : ℕ) (m : M) (r : Fin (n + 1) → R) :
    (barObjIso k R M n).hom.hom
      (((barK k R M).δ (0 : Fin (n + 2))).hom
        ((barObjIso k R M (n + 1)).inv.hom (m ⊗ₜ[k] PiTensorProduct.tprod k r))) =
      (MulOpposite.op (r 0) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst r) := by
  rw [barObjIso_inv_tprod]
  rw [show (barK k R M).δ (0 : Fin (n + 2)) =
      Monad.barFaceApp
        (T := tensorMonad k R) (R := forgetRightModule k R)
        (L := Monad.algebraLeftModule (bimoduleAlgebra k R M))
        n 0 ⟨PUnit.unit⟩ by
    simpa only [barK, SimplicialObject.δ_def] using
      (Monad.algebraBar_map_δ_op (forgetRightModule k R)
        (bimoduleAlgebra k R M) (0 : Fin (n + 2)))]
  rw [Monad.barFaceApp_of_val_zero (hi := rfl)]
  change (barObjIso k R M n).hom.hom
    ((Monad.rightActionPow (tensorMonad k R)
      (forgetRightModule k R) n (ModuleCat.of Rᵐᵒᵖ M)).hom
        (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) (n + 1) r m)) = _
  rw [rightActionPow_rawPure, barObjIso_hom_rawPure]

/-- The interior faces multiply adjacent factors in their source order. -/
theorem bar_face_inner (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
    (n : ℕ) (i : Fin n) (m : M) (r : Fin (n + 1) → R) :
    (barObjIso k R M n).hom.hom
      (((barK k R M).δ i.castSucc.succ).hom
        ((barObjIso k R M (n + 1)).inv.hom (m ⊗ₜ[k] PiTensorProduct.tprod k r))) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i r) := by
  rw [barObjIso_inv_tprod]
  rw [show (barK k R M).δ i.castSucc.succ =
      Monad.barFaceApp
        (T := tensorMonad k R) (R := forgetRightModule k R)
        (L := Monad.algebraLeftModule (bimoduleAlgebra k R M))
        n i.castSucc.succ ⟨PUnit.unit⟩ by
    simpa only [barK, SimplicialObject.δ_def] using
      (Monad.algebraBar_map_δ_op (forgetRightModule k R)
        (bimoduleAlgebra k R M) i.castSucc.succ)]
  rw [Monad.barFaceApp_of_middle (k := i) (hk := rfl)]
  change (barObjIso k R M n).hom.hom
    (((forgetRight k R).map
      (Monad.barMuAtPos (tensorMonad k R) n i
        (ModuleCat.of Rᵐᵒᵖ M))).hom
          (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) (n + 1) r m)) = _
  rw [barMuAtPos_rawPure, barObjIso_hom_rawPure]

/-- The last face is the left coefficient action in tensor coordinates. -/
theorem bar_face_last (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
    (n : ℕ) (m : M) (r : Fin (n + 1) → R) :
    (barObjIso k R M n).hom.hom
      (((barK k R M).δ (Fin.last (n + 1))).hom
        ((barObjIso k R M (n + 1)).inv.hom (m ⊗ₜ[k] PiTensorProduct.tprod k r))) =
      (r (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast r) := by
  rw [barObjIso_inv_tprod]
  rw [show (barK k R M).δ (Fin.last (n + 1)) =
      Monad.barFaceApp
        (T := tensorMonad k R) (R := forgetRightModule k R)
        (L := Monad.algebraLeftModule (bimoduleAlgebra k R M))
        n (Fin.last (n + 1)) ⟨PUnit.unit⟩ by
    simpa only [barK, SimplicialObject.δ_def] using
      (Monad.algebraBar_map_δ_op (forgetRightModule k R)
        (bimoduleAlgebra k R M) (Fin.last (n + 1)))]
  rw [Monad.barFaceApp_of_val_last (hi := rfl)]
  change (barObjIso k R M n).hom.hom
    (((forgetRight k R).map
      ((Monad.monadPow (tensorMonad k R) n).map
        (bimoduleAlgebra k R M).a)).hom
          (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) (n + 1) r m)) = _
  rw [algebraAction_rawPure, barObjIso_hom_rawPure]

/-- Native degeneracy has the internally proved unit-insertion formula. -/
theorem bar_degen_insert (k : Type u) (R : Type v) (M : Type (max u v w)) [CommRing k] [Ring R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [Module k M] [SMulCommClass R Rᵐᵒᵖ M] [SMulCommClass k R M]
    [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
    (n : ℕ) (i : Fin (n + 1)) (m : M) (r : Fin n → R) :
    (barObjIso k R M (n + 1)).hom.hom
      (((barK k R M).σ i).hom
        ((barObjIso k R M n).inv.hom (m ⊗ₜ[k] PiTensorProduct.tprod k r))) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildInsertOne i r) := by
  rw [barObjIso_inv_tprod]
  rw [show (barK k R M).σ i =
      (forgetRight k R).map
        (Monad.barEtaAtPos (tensorMonad k R) n i
          (ModuleCat.of Rᵐᵒᵖ M)) by
    change
      (Monad.algebraBar (forgetRightModule k R)
        (bimoduleAlgebra k R M)).map (SimplexCategory.σ i).op =
          (forgetRightModule k R).functor.map
            (Monad.barEtaAtPos (tensorMonad k R) n i
              (bimoduleAlgebra k R M).A)
    exact Monad.algebraBar_map_σ_op (forgetRightModule k R)
      (bimoduleAlgebra k R M) i]
  change (barObjIso k R M (n + 1)).hom.hom
    (((forgetRight k R).map
      (Monad.barEtaAtPos (tensorMonad k R) n i
        (ModuleCat.of Rᵐᵒᵖ M))).hom
          (rawPure k R (ModuleCat.of Rᵐᵒᵖ M) n r m)) = _
  rw [barEtaAtPos_rawPure, barObjIso_hom_rawPure]


section IndependentCoefficients

variable (k : Type u) (A : Type v) (M : Type w)
  [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M]
  [Module A M] [Module Aᵐᵒᵖ M] [Module k M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Scalar commutation on the native lift follows from scalar commutation on its carrier. -/
local instance uliftSMulCommClass {S T X : Type*} [SMul S X] [SMul T X]
    [SMulCommClass S T X] : SMulCommClass S T (ULift X) where
  smul_comm s t x := ULift.ext (smul_comm s t x.down)

/-- The monadic coefficient bar, with only the coefficient universe lifted. -/
noncomputable def coefficientBar : SimplicialObject (ModuleCat.{max u v w} k) :=
  barK k A (ULift.{max u v w} M)

/-- The literal printed tensor level. The coefficient universe is independent of the algebra. -/
abbrev chainLevel (n : ℕ) : ModuleCat.{max u v w} k :=
  ModuleCat.of k (M ⊗[k] TensorPower k n A)

/-- Canonical coordinates of the coefficient bar; no comparison is supplied by callers. -/
noncomputable def coefficientBarObjIso (n : ℕ) :
    (coefficientBar k A M).obj (Opposite.op (SimplexCategory.mk n)) ≅ chainLevel k A M n :=
  barObjIso k A (ULift.{max u v w} M) n ≪≫
    (TensorProduct.congr (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))).toModuleIso

@[simp]
theorem coefficientBarObjIso_hom_rawPure (n : ℕ) (m : M) (a : Fin n → A) :
    (coefficientBarObjIso k A M n).hom.hom
      (rawPure k A (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v w} M)) n a (ULift.up m)) =
        m ⊗ₜ[k] PiTensorProduct.tprod k a := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))
      ((barObjIso k A (ULift.{max u v w} M) n).hom.hom
        (rawPure k A (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v w} M)) n a (ULift.up m))) = _
  rw [barObjIso_hom_rawPure]
  rfl

@[simp]
theorem coefficientBarObjIso_inv_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    (coefficientBarObjIso k A M n).inv.hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      rawPure k A (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v w} M)) n a (ULift.up m) := by
  change (barObjIso k A (ULift.{max u v w} M) n).inv.hom
      ((TensorProduct.congr
        (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
        (LinearEquiv.refl k (TensorPower k n A))).symm
          (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [TensorProduct.congr_symm_tmul]
  exact barObjIso_inv_tprod k A (ULift.{max u v w} M) n a (ULift.up m)

/-- An actual Hochschild face in the literal tensor coordinates. -/
noncomputable def face (n : ℕ) (i : Fin (n + 2)) :
    chainLevel k A M (n + 1) ⟶ chainLevel k A M n :=
  (coefficientBarObjIso k A M (n + 1)).inv ≫
    (coefficientBar k A M).δ i ≫ (coefficientBarObjIso k A M n).hom

/-- The first endpoint uses the right coefficient action. -/
@[simp]
theorem face_first_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    (face k A M n 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (MulOpposite.op (a 0) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a) := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))
      ((barObjIso k A (ULift.{max u v w} M) n).hom.hom
        (((barK k A (ULift.{max u v w} M)).δ 0).hom
          ((barObjIso k A (ULift.{max u v w} M) (n + 1)).inv.hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  exact (congrArg
    (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A)))
    (bar_face_first k A (ULift.{max u v w} M) n (ULift.up m) a)).trans (by rfl)

/-- Each interior endpoint multiplies adjacent algebra factors in their given order. -/
@[simp]
theorem face_inner_tprod (n : ℕ) (i : Fin n) (m : M) (a : Fin (n + 1) → A) :
    (face k A M n i.castSucc.succ).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i a) := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))
      ((barObjIso k A (ULift.{max u v w} M) n).hom.hom
        (((barK k A (ULift.{max u v w} M)).δ i.castSucc.succ).hom
          ((barObjIso k A (ULift.{max u v w} M) (n + 1)).inv.hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  exact (congrArg
    (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A)))
    (bar_face_inner k A (ULift.{max u v w} M) n i (ULift.up m) a)).trans (by rfl)

/-- The last endpoint uses the left coefficient action. -/
@[simp]
theorem face_last_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    (face k A M n (Fin.last (n + 1))).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A))
      ((barObjIso k A (ULift.{max u v w} M) n).hom.hom
        (((barK k A (ULift.{max u v w} M)).δ (Fin.last (n + 1))).hom
          ((barObjIso k A (ULift.{max u v w} M) (n + 1)).inv.hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  exact (congrArg
    (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k n A)))
    (bar_face_last k A (ULift.{max u v w} M) n (ULift.up m) a)).trans (by rfl)

/-- The three printed face formulas in one total, endpoint-sensitive function. -/
noncomputable def faceValue (n : ℕ) (i : Fin (n + 2)) (m : M) (a : Fin (n + 1) → A) :
    M ⊗[k] TensorPower k n A :=
  Fin.cases
    ((MulOpposite.op (a 0) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a))
    (Fin.lastCases
      ((a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a))
      (fun j : Fin n => m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent j a))) i

/-- Every face of the complex has the printed generator formula. -/
theorem face_tprod (n : ℕ) (i : Fin (n + 2)) (m : M) (a : Fin (n + 1) → A) :
    (face k A M n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      faceValue k A M n i m a := by
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · simpa only [faceValue, Fin.cases_zero] using face_first_tprod k A M n m a
  · simp only [faceValue, Fin.cases_succ, Fin.lastCases_last]
    simpa only [Fin.succ_last] using face_last_tprod k A M n m a
  · simpa only [faceValue, Fin.cases_succ, Fin.lastCases_castSucc] using
      face_inner_tprod k A M n l m a

/-- The native alternating face-map complex of the coefficient bar. -/
noncomputable def nativeComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (coefficientBar k A M)

/-- The literal Hochschild boundary is the transported native alternating differential. -/
noncomputable def boundary (n : ℕ) : chainLevel k A M (n + 1) ⟶ chainLevel k A M n :=
  (coefficientBarObjIso k A M (n + 1)).inv ≫
    (nativeComplex k A M).d (n + 1) n ≫ (coefficientBarObjIso k A M n).hom

/-- Square-zero follows from the complex and the internal degree isomorphisms. -/
theorem boundary_squared (n : ℕ) : boundary k A M (n + 1) ≫ boundary k A M n = 0 := by
  change
    ((coefficientBarObjIso k A M (n + 2)).inv ≫
      (AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (n + 2) (n + 1) ≫
        (coefficientBarObjIso k A M (n + 1)).hom) ≫
    ((coefficientBarObjIso k A M (n + 1)).inv ≫
      (AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (n + 1) n ≫
        (coefficientBarObjIso k A M n).hom) = 0
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    ((AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (n + 2) (n + 1)),
    HomologicalComplex.d_comp_d, zero_comp, comp_zero]

/-- The chain complex on the literal printed objects, constructed from the bar. -/
noncomputable def chainComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (chainLevel k A M) (boundary k A M) (boundary_squared k A M)

@[simp]
theorem chainComplex_X (n : ℕ) : (chainComplex k A M).X n = chainLevel k A M n := rfl

@[simp]
theorem chainComplex_d (n : ℕ) :
    (chainComplex k A M).d (n + 1) n = boundary k A M n :=
  ChainComplex.of_d _ _ _

/-- A comparison to the existing native monadic-bar complex. -/
noncomputable def chainComplexIso : chainComplex k A M ≅ nativeComplex k A M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientBarObjIso k A M n).symm) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      rw [chainComplex_d]
      change (coefficientBarObjIso k A M (j + 1)).inv ≫
          (AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (j + 1) j =
        ((coefficientBarObjIso k A M (j + 1)).inv ≫
          (AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (j + 1) j ≫
            (coefficientBarObjIso k A M j).hom) ≫
          (coefficientBarObjIso k A M j).inv
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- The transported boundary is the complete alternating sum of the faces. -/
theorem boundary_eq_sum (n : ℕ) :
    boundary k A M n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • face k A M n i := by
  change (coefficientBarObjIso k A M (n + 1)).inv ≫
      (AlternatingFaceMapComplex.obj (coefficientBar k A M)).d (n + 1) n ≫
        (coefficientBarObjIso k A M n).hom = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, face]

/-- The source formula, in every degree and with both coefficient endpoints present. -/
theorem boundary_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    (boundary k A M n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • faceValue k A M n i m a := by
  rw [boundary_eq_sum]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : M ⊗[k] TensorPower k n A => (-1 : ℤ) ^ i.val • z)
    (face_tprod k A M n i m a)

/-- The degree-one boundary is right action minus left action, as a literal tensor equation. -/
theorem boundary_one_tprod (m : M) (a : Fin 1 → A) :
    (boundary k A M 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (MulOpposite.op (a 0) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a) -
        (a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) := by
  rw [boundary_tprod, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
  rfl

/-- The printed Hochschild homology is the homology of this actual literal complex. -/
noncomputable def homology (n : ℕ) : ModuleCat.{max u v w} k :=
  (chainComplex k A M).homology n

end IndependentCoefficients

/-- Pure coefficient tensors with a tensor tuple determine a linear map of semimodules. -/
theorem tensorPower_ext {k : Type u} [CommSemiring k] {A : Type v}
    [AddCommMonoid A] [Module k A]
    {M N : Type*} [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]
    {n : ℕ} {f g : M ⊗[k] TensorPower k n A →ₗ[k] N}
    (h : ∀ (m : M) (a : Fin n → A),
      f (m ⊗ₜ[k] PiTensorProduct.tprod k a) = g (m ⊗ₜ[k] PiTensorProduct.tprod k a)) :
    f = g := by
  apply TensorProduct.ext'
  intro m z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
      simp only [TensorProduct.tmul_smul, map_smul, h]
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]

end ModuleCat.Algebra.Hochschild
