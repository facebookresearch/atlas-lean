/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit.lean`
and
`P2M/Sol/S_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.LinearAlgebra.Dual.Basis
import MathlibExt.Algebra.Algebra.HopfAlgebra.ComulAntipode
import MathlibExt.RingTheory.HopfAlgebra.HopfKer
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Left integrals on a finite free Hopf algebra

For a finite free commutative Hopf algebra `B` over a commutative ring `R`, the dual
`Module.Dual R B` is a right Hopf module over `B`, and the fundamental theorem of Hopf
modules produces finitely many left integrals `Λ j` together with elements `u j` such that
`∑ j, Λ j (u j * b) = ε b` for every `b : B`.
-/

@[expose] public section

open Coalgebra HopfAlgebra WithConv
open scoped TensorProduct Coalgebra.TensorProduct

universe u v w

namespace HopfAlgebra.LeftIntegral

section Abstract

variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

private def RightComodule.coinvariants (ρ : M →ₗ[k] M ⊗[k] H) : Submodule k M :=
  LinearMap.ker (ρ - (TensorProduct.mk k M H).flip 1)

omit [Module H M] [IsScalarTower k H M] in
@[local simp] private theorem RightComodule.mem_coinvariants (ρ : M →ₗ[k] M ⊗[k] H) (m : M) :
    m ∈ RightComodule.coinvariants ρ ↔ ρ m = m ⊗ₜ[k] (1 : H) := by
  simp [RightComodule.coinvariants, sub_eq_zero]


private noncomputable def RightComodule.actMap (ρ : M →ₗ[k] M ⊗[k] H) :
    (RightComodule.coinvariants ρ) ⊗[k] H →ₗ[k] M :=
  TensorProduct.lift
    { toFun := fun n =>
        { toFun := fun h => h • (n : M)
          map_add' := fun _ _ => add_smul _ _ _
          map_smul' := fun c h => by
            simp only [RingHom.id_apply, smul_assoc] }
      map_add' := fun x y => by ext h; simp [smul_add]
      map_smul' := fun c x => by ext h; simp [smul_comm c] }

@[local simp] private theorem RightComodule.actMap_tmul (ρ : M →ₗ[k] M ⊗[k] H)
    (n : RightComodule.coinvariants ρ) (h : H) :
    RightComodule.actMap ρ (n ⊗ₜ[k] h) = h • (n : M) := rfl

end Abstract

section FTHM

attribute [local simp] RightComodule.mem_coinvariants RightComodule.actMap_tmul


variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
  [SMulCommClass k H M]

namespace RightHopfModule

private noncomputable def hsmul : H ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift
    { toFun := fun h =>
        { toFun := fun m => h • m
          map_add' := fun _ _ => smul_add _ _ _
          map_smul' := fun c m => smul_comm h c m }
      map_add' := fun h h' => by ext m; simp [add_smul]
      map_smul' := fun c h => by ext m; simp [smul_assoc] }

omit [SMulCommClass k H M] in
@[local simp] private theorem hsmul_tmul (h : H) (m : M) : hsmul (k := k) (h ⊗ₜ[k] m) = h • m := rfl

private noncomputable def smulAt (n : M) : H →ₗ[k] M where
  toFun h := h • n
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := smul_assoc _ _ _

omit [SMulCommClass k H M] in
@[local simp] private theorem smulAt_apply (n : M) (h : H) : smulAt (k := k) n h = h • n := rfl

end RightHopfModule

attribute [local simp] RightHopfModule.hsmul_tmul RightHopfModule.smulAt_apply

private structure RightHopfModule (ρ : M →ₗ[k] M ⊗[k] H) : Prop where

  coaction_counit :
    (Coalgebra.counit (R := k) (A := H)).lTensor M ∘ₗ ρ = (TensorProduct.mk k M k).flip 1
  coaction_coassoc :
    ρ.rTensor H ∘ₗ ρ
      = (TensorProduct.assoc k M H H).symm.toLinearMap
          ∘ₗ (Coalgebra.comul (R := k) (A := H)).lTensor M ∘ₗ ρ
  coaction_compat :
    ρ ∘ₗ RightHopfModule.hsmul
      = TensorProduct.map RightHopfModule.hsmul (LinearMap.mul' k H)
          ∘ₗ (TensorProduct.tensorTensorTensorComm k H H M H).toLinearMap
          ∘ₗ TensorProduct.map (Coalgebra.comul (R := k) (A := H)) ρ

namespace RightHopfModule

variable {ρ : M →ₗ[k] M ⊗[k] H}

omit [SMulCommClass k H M] in
private theorem compat_apply (R : RightHopfModule ρ) (h : H) (m : M) :
    ρ (h • m) = TensorProduct.map hsmul (LinearMap.mul' k H)
        ((TensorProduct.tensorTensorTensorComm k H H M H) (Coalgebra.comul h ⊗ₜ[k] ρ m)) := by
  have := LinearMap.congr_fun R.coaction_compat (h ⊗ₜ[k] m)
  simpa using this

omit [SMulCommClass k H M] in
private theorem counit_coaction (R : RightHopfModule ρ) (m : M) :
    (TensorProduct.rid k M) ((Coalgebra.counit (R := k) (A := H)).lTensor M (ρ m)) = m := by
  have := LinearMap.congr_fun R.coaction_counit m
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply] at this
  rw [this]; simp

private noncomputable def coinvProjAux (ρ : M →ₗ[k] M ⊗[k] H) : M →ₗ[k] M :=
  hsmul ∘ₗ (HopfAlgebra.antipode k (A := H)).rTensor M
    ∘ₗ (TensorProduct.comm k M H).toLinearMap ∘ₗ ρ

private noncomputable def chi (n : M) : H ⊗[k] (H ⊗[k] H) →ₗ[k] M ⊗[k] H :=
  TensorProduct.map (smulAt (k := k) (H := H) n) (LinearMap.mul' k H)
    ∘ₗ TensorProduct.map (HopfAlgebra.antipode k)
        (TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id)
    ∘ₗ (TensorProduct.assoc k H H H).toLinearMap
    ∘ₗ (TensorProduct.comm k H (H ⊗[k] H)).toLinearMap
    ∘ₗ (TensorProduct.comm k H H).lTensor H

omit [SMulCommClass k H M] in
@[local simp] private theorem chi_tmul (n : M) (p q r : H) :
    chi (k := k) n (p ⊗ₜ[k] (q ⊗ₜ[k] r))
      = ((HopfAlgebra.antipode k r) • n) ⊗ₜ[k] ((HopfAlgebra.antipode k q) * p) := by
  simp [chi]

omit [SMulCommClass k H M] in
private theorem coinvProjAux_mem_coinvariants (R : RightHopfModule ρ) (m : M) :
    coinvProjAux ρ m ∈ RightComodule.coinvariants ρ := by
  rw [RightComodule.mem_coinvariants]
  set Φ : (M ⊗[k] H) ⊗[k] H →ₗ[k] M ⊗[k] H :=
    TensorProduct.map hsmul (LinearMap.mul' k H)
      ∘ₗ (TensorProduct.tensorTensorTensorComm k H H M H).toLinearMap
      ∘ₗ (TensorProduct.comm k (M ⊗[k] H) (H ⊗[k] H)).toLinearMap
      ∘ₗ (Coalgebra.comul ∘ₗ HopfAlgebra.antipode k (A := H)).lTensor (M ⊗[k] H) with hΦ
  have hΦtmul : ∀ (w : M ⊗[k] H) (h : H),
      Φ (w ⊗ₜ[k] h) = TensorProduct.map hsmul (LinearMap.mul' k H)
          ((TensorProduct.tensorTensorTensorComm k H H M H)
            (Coalgebra.comul (HopfAlgebra.antipode k h) ⊗ₜ[k] w)) := fun w h => by
    simp only [hΦ, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
      LinearEquiv.coe_coe, TensorProduct.comm_tmul]
  have step1 : ρ (coinvProjAux ρ m) = Φ ((ρ.rTensor H) (ρ m)) := by
    simp only [coinvProjAux, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    induction ρ m with
    | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
    | tmul n h =>
        simp only [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, hsmul_tmul,
          R.compat_apply, hΦtmul]
  have step2 : (ρ.rTensor H) (ρ m)
      = (TensorProduct.assoc k M H H).symm
          ((Coalgebra.comul (R := k) (A := H)).lTensor M (ρ m)) := by
    have := LinearMap.congr_fun R.coaction_coassoc m; simpa using this
  have step3 : ∀ (n : M) (h : H),
      Φ ((TensorProduct.assoc k M H H).symm (n ⊗ₜ[k] Coalgebra.comul h))
        = ((HopfAlgebra.antipode k h) • n) ⊗ₜ[k] (1 : H) := by
    intro n h
    have ha : ∀ z : H ⊗[k] H,
        Φ ((TensorProduct.assoc k M H H).symm (n ⊗ₜ[k] z))
          = chi (k := k) n ((Coalgebra.comul (R := k) (A := H)).lTensor H z) := by
      intro z
      induction z with
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add] at *; rw [hx, hy]
      | tmul g h' =>
          simp only [TensorProduct.assoc_symm_tmul, hΦ, LinearMap.coe_comp,
            Function.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
            TensorProduct.comm_tmul, HopfAlgebra.comul_antipode]
          induction Coalgebra.comul (R := k) h' with
          | add x y hx hy =>
              simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul] at *
              rw [hx, hy]
          | tmul p q =>
              simp only [TensorProduct.map_tmul, TensorProduct.comm_tmul,
                TensorProduct.tensorTensorTensorComm_tmul, hsmul_tmul,
                LinearMap.mul'_apply, chi_tmul]
    rw [ha (Coalgebra.comul h), ← Coalgebra.coassoc_apply]
    have hb : ∀ (w : H ⊗[k] H) (r : H),
        chi (k := k) n ((TensorProduct.assoc k H H H) (w ⊗ₜ[k] r))
          = ((HopfAlgebra.antipode k r) • n)
              ⊗ₜ[k] (LinearMap.mul' k H ((HopfAlgebra.antipode k).lTensor H w)) := by
      intro w r
      induction w with
      | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add] at *
          rw [hx, hy]
      | tmul p q => simp [mul_comm]
    have hc : ∀ z : H ⊗[k] H,
        chi (k := k) n ((TensorProduct.assoc k H H H)
            ((Coalgebra.comul (R := k) (A := H)).rTensor H z))
          = TensorProduct.map
              (smulAt (k := k) (H := H) n ∘ₗ HopfAlgebra.antipode k)
              (Algebra.linearMap k H)
              ((TensorProduct.comm k k H).toLinearMap
                ((Coalgebra.counit (R := k) (A := H)).rTensor H z)) := by
      intro z
      induction z with
      | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
      | tmul G r =>
          simp only [LinearMap.rTensor_tmul, hb (Coalgebra.comul G) r,
            _root_.HopfAlgebra.mul_antipode_lTensor_comul_apply, TensorProduct.comm_tmul,
            TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply, smulAt_apply,
            Algebra.linearMap_apply, LinearEquiv.coe_coe]
    rw [hc (Coalgebra.comul h), Coalgebra.rTensor_counit_comul]
    simp
  rw [step1, step2]
  simp only [coinvProjAux, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  induction ρ m with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul] at *; rw [hx, hy]
  | tmul n h =>
      simp only [LinearMap.lTensor_tmul, step3, TensorProduct.comm_tmul,
        LinearMap.rTensor_tmul, hsmul_tmul]

private noncomputable def invActMap (R : RightHopfModule ρ) :
    M →ₗ[k] RightComodule.coinvariants ρ ⊗[k] H :=
  (LinearMap.codRestrict (RightComodule.coinvariants ρ) (coinvProjAux ρ)
      (R.coinvProjAux_mem_coinvariants)).rTensor H ∘ₗ ρ

omit [SMulCommClass k H M] in
private theorem actMap_invActMap (R : RightHopfModule ρ) (m : M) :
    RightComodule.actMap ρ (R.invActMap m) = m := by
  have key : RightComodule.actMap ρ (R.invActMap m)
      = hsmul (k := k) ((TensorProduct.comm k M H)
          (((coinvProjAux ρ).rTensor H) (ρ m))) := by
    simp only [invActMap, LinearMap.coe_comp, Function.comp_apply]
    induction ρ m with
    | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
    | tmul n h =>
        simp only [LinearMap.rTensor_tmul, RightComodule.actMap_tmul,
          LinearMap.codRestrict_apply, TensorProduct.comm_tmul, hsmul_tmul]
  rw [key]
  have expand : ((coinvProjAux ρ).rTensor H) (ρ m)
      = (hsmul ∘ₗ (HopfAlgebra.antipode k).rTensor M
            ∘ₗ (TensorProduct.comm k M H).toLinearMap).rTensor H
          ((TensorProduct.assoc k M H H).symm
            ((Coalgebra.comul (R := k) (A := H)).lTensor M (ρ m))) := by
    rw [show ((coinvProjAux ρ).rTensor H) (ρ m)
          = ((hsmul ∘ₗ (HopfAlgebra.antipode k).rTensor M
                ∘ₗ (TensorProduct.comm k M H).toLinearMap).rTensor H)
              ((ρ.rTensor H) (ρ m)) from by
        simp only [coinvProjAux, LinearMap.rTensor_comp, LinearMap.comp_apply]]
    congr 1; have := LinearMap.congr_fun R.coaction_coassoc m; simpa using this
  rw [expand]; conv_rhs => rw [← R.counit_coaction m]
  induction ρ m with
  | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
  | tmul n h =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      have reorder : ∀ z : H ⊗[k] H,
          hsmul (k := k) ((TensorProduct.comm k M H)
              (((hsmul ∘ₗ (HopfAlgebra.antipode k).rTensor M
                    ∘ₗ (TensorProduct.comm k M H).toLinearMap).rTensor H)
                ((TensorProduct.assoc k M H H).symm (n ⊗ₜ[k] z))))
            = smulAt (k := k) (H := H) n
                (LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H z)) := by
        intro z
        induction z with
        | add x y hx hy =>
            simp only [TensorProduct.tmul_add, map_add] at *; rw [hx, hy]
        | tmul p q =>
            simp [mul_comm, mul_smul]
      rw [reorder (Coalgebra.comul h),
        _root_.HopfAlgebra.mul_antipode_rTensor_comul_apply, smulAt_apply,
        algebraMap_smul]

end RightHopfModule

end FTHM



section DualHopfModule

attribute [local simp] RightComodule.mem_coinvariants RightComodule.actMap_tmul
attribute [local simp] RightHopfModule.hsmul_tmul RightHopfModule.smulAt_apply

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [HopfAlgebra R B]

private noncomputable def dconv (f m : Module.Dual R B) : Module.Dual R B :=
  LinearMap.mul' R R ∘ₗ TensorProduct.map f m ∘ₗ Coalgebra.comul

private theorem toConv_dconv (f m : Module.Dual R B) :
    toConv (dconv f m) = toConv f * toConv m := rfl

private theorem dconv_apply_repr (f m : Module.Dual R B) {x : B} {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr R x ι𝓡) :
    dconv f m x = ∑ i ∈ 𝓡.index, f (𝓡.left i) * m (𝓡.right i) := by
  simp only [dconv, LinearMap.coe_comp, Function.comp_apply, ← 𝓡.eq, map_sum,
    TensorProduct.map_tmul, LinearMap.mul'_apply]

private theorem dconv_assoc (f g m : Module.Dual R B) : dconv (dconv f g) m = dconv f (dconv g m) :=
  toConv_injective (by simp only [toConv_dconv, mul_assoc])

private theorem dconv_add_left (f g m : Module.Dual R B) :
    dconv (f + g) m = dconv f m + dconv g m := by
  simp only [dconv, TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add]

private theorem dconv_smul_left (r : R) (f m : Module.Dual R B) :
    dconv (r • f) m = r • dconv f m := by
  simp only [dconv, TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]

private theorem dconv_add_right (f m m' : Module.Dual R B) :
    dconv f (m + m') = dconv f m + dconv f m' := by
  simp only [dconv, TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]

private theorem dconv_smul_right (r : R) (f m : Module.Dual R B) :
    dconv f (r • m) = r • dconv f m := by
  simp only [dconv, TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul]

private theorem dconv_sum_left {ι : Type*} (s : Finset ι) (f : ι → Module.Dual R B)
    (m : Module.Dual R B) :
    dconv (∑ i ∈ s, f i) m = ∑ i ∈ s, dconv (f i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => ext x; simp [dconv]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dconv_add_left, ih]

private theorem dconv_counit_left (m : Module.Dual R B) : dconv (Coalgebra.counit) m = m := by
  ext x
  rw [dconv_apply_repr _ _ (ℛ R x)]
  simp_rw [← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]

@[reducible] private noncomputable def dualSMul : SMul B (Module.Dual R B) :=
  ⟨fun b m => m ∘ₗ LinearMap.mulRight R (antipode R b)⟩

attribute [local instance] dualSMul

@[local simp] private theorem dual_smul_apply (b : B) (m : Module.Dual R B) (x : B) :
    (b • m) x = m (x * antipode R b) := rfl

@[reducible] private noncomputable def dualModule : Module B (Module.Dual R B) where
  one_smul m := by ext x; simp
  mul_smul b b' m := by
    ext x; simp only [dual_smul_apply, HopfAlgebra.antipode_mul_antidistrib]; congr 1; ring
  smul_zero b := by ext x; simp
  smul_add b m m' := by ext x; simp
  add_smul b b' m := by ext x; simp [mul_add]
  zero_smul m := by ext x; simp

attribute [local instance] dualModule

private theorem dual_isScalarTower : IsScalarTower R B (Module.Dual R B) :=
  ⟨fun r b m => by ext x; simp⟩

private theorem dual_smulCommClass : SMulCommClass R B (Module.Dual R B) :=
  ⟨fun r b m => by ext x; simp⟩

attribute [local instance] dual_isScalarTower dual_smulCommClass

variable [Module.Finite R B] [Module.Free R B]

private noncomputable abbrev bB : Module.Basis (Module.Free.ChooseBasisIndex R B) R B :=
  Module.Free.chooseBasis R B

private noncomputable def dconvLeft (f : Module.Dual R B) :
    Module.Dual R B →ₗ[R] Module.Dual R B where
  toFun m := dconv f m
  map_add' m m' := dconv_add_right f m m'
  map_smul' r m := dconv_smul_right r f m

omit [Module.Finite R B] [Module.Free R B] in
@[local simp] private theorem dconvLeft_apply (f m : Module.Dual R B) :
    dconvLeft f m = dconv f m := rfl

private noncomputable def dualCoaction : Module.Dual R B →ₗ[R] Module.Dual R B ⊗[R] B :=
  ∑ i, (TensorProduct.mk R (Module.Dual R B) B).flip (bB i)
    ∘ₗ dconvLeft ((bB (R := R) (B := B)).coord i)

private theorem dualCoaction_apply (m : Module.Dual R B) :
    dualCoaction m = ∑ i, dconv ((bB (R := R) (B := B)).coord i) m ⊗ₜ[R] bB i := by
  simp [dualCoaction]

private theorem tmul_eq_sum_coord {N : Type*} [AddCommGroup N] [Module R N] (n : N) (y : B) :
    n ⊗ₜ[R] y = ∑ l, ((bB (R := R) (B := B)).coord l y • n) ⊗ₜ[R] bB l := by
  conv_lhs => rw [← (bB (R := R) (B := B)).sum_repr y]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Module.Basis.coord_apply]

private noncomputable def coeff2 (j l : Module.Free.ChooseBasisIndex R B) : B ⊗[R] B →ₗ[R] R :=
  LinearMap.mul' R R ∘ₗ TensorProduct.map ((bB (R := R) (B := B)).coord
      j) ((bB (R := R) (B := B)).coord l)

private theorem eq_sum_coeff2 (z : B ⊗[R] B) :
    z = ∑ j, ∑ l, coeff2 j l z • (bB (R := R) (B := B) j ⊗ₜ[R] bB l) := by
  induction z with
  | add x y hx hy =>
      conv_lhs => rw [hx, hy]
      simp only [map_add, add_smul, Finset.sum_add_distrib]
  | tmul x y =>
      conv_lhs => rw [← (bB (R := R) (B := B)).sum_repr x, ← (bB (R := R) (B := B)).sum_repr y]
      simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul,
        coeff2, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply, Module.Basis.coord_apply]
      exact Finset.sum_comm

omit [Module.Finite R B] in
private theorem coeff2_comul (j l : Module.Free.ChooseBasisIndex R B) (b : B) :
    coeff2 j l (Coalgebra.comul (R := R) b)
      = dconv ((bB (R := R) (B := B)).coord j) ((bB (R := R) (B := B)).coord l) b := rfl

private theorem sum_apply_smul_dconv_coord (f m : Module.Dual R B) :
    ∑ i, f (bB i) • dconv ((bB (R := R) (B := B)).coord i) m = dconv f m := by
  simp_rw [← dconv_smul_left]
  rw [← dconv_sum_left, Module.Basis.sum_dual_apply_smul_coord]

private theorem dualCoaction_counit :
    (Coalgebra.counit (R := R) (A := B)).lTensor (Module.Dual R B) ∘ₗ dualCoaction
      = (TensorProduct.mk R (Module.Dual R B) R).flip 1 := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, dualCoaction_apply, map_sum,
    LinearMap.lTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply]
  have : ∀ i, dconv ((bB (R := R) (B := B)).coord i) m ⊗ₜ[R] (Coalgebra.counit (R := R)
      (bB (R := R) (B := B) i))
      = (Coalgebra.counit (R := R) (bB (R := R) (B := B) i) • dconv
          ((bB (R := R) (B := B)).coord i) m)
          ⊗ₜ[R] (1 : R) := fun i => by
    rw [TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  simp_rw [this, ← TensorProduct.sum_tmul, sum_apply_smul_dconv_coord, dconv_counit_left]

private theorem dualCoaction_coassoc :
    (dualCoaction (R := R) (B := B)).rTensor B ∘ₗ dualCoaction
      = (TensorProduct.assoc R (Module.Dual R B) B B).symm.toLinearMap
          ∘ₗ (Coalgebra.comul (R := R) (A := B)).lTensor (Module.Dual R B)
          ∘ₗ (dualCoaction (R := R) (B := B)) := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, dualCoaction_apply, map_sum,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.sum_tmul]
  have hR : ∀ i, (TensorProduct.assoc R (Module.Dual R B) B B).symm.toLinearMap
        (dconv ((bB (R := R) (B := B)).coord i) m ⊗ₜ[R] Coalgebra.comul (R := R)
            (bB (R := R) (B := B) i))
      = ∑ j, ∑ l, coeff2 j l (Coalgebra.comul (R := R) (bB (R := R) (B := B) i))
          • ((dconv ((bB (R := R) (B := B)).coord i) m ⊗ₜ[R] bB j) ⊗ₜ[R] bB l) := fun i => by
    conv_lhs => rw [eq_sum_coeff2 (Coalgebra.comul (R := R) (bB (R := R) (B := B) i))]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul]
    simp only [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul]
  simp_rw [hR, coeff2_comul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp_rw [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, sum_apply_smul_dconv_coord,
      dconv_assoc]

omit [Module.Finite R B] in
omit [Module.Free R B] in
private theorem compat_core (f m : Module.Dual R B) (b c d : B) {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr R b ι𝓡)
    {κ𝓡₁ : ι𝓡 → Type*} (𝓡₁ : (i : ι𝓡) → Coalgebra.Repr R (𝓡.left i) (κ𝓡₁ i)) :
    ∑ i ∈ 𝓡.index, ∑ k ∈ (𝓡₁ i).index,
        f (𝓡.right i * (c * antipode R ((𝓡₁ i).right k))) * m (d * antipode R ((𝓡₁ i).left k))
      = f c * m (d * antipode R b) := by
  let 𝓡₂ := fun (i : ι𝓡) => ℛ R (𝓡.right i)
  let φ₁ : Module.Dual R B := m ∘ₗ LinearMap.mulLeft R d ∘ₗ antipode R
  let ψ : B ⊗[R] B →ₗ[R] R :=
    f ∘ₗ LinearMap.mulRight R c ∘ₗ LinearMap.mul' R B ∘ₗ (antipode R).rTensor B
  let Φ : B ⊗[R] (B ⊗[R] B) →ₗ[R] R := LinearMap.mul' R R ∘ₗ TensorProduct.map φ₁ ψ
  have hΦ : ∀ p q r : B, Φ (p ⊗ₜ[R] (q ⊗ₜ[R] r))
      = m (d * antipode R p) * f (antipode R q * r * c) := by
    intro p q r; simp [Φ, φ₁, ψ]
  have key := congr(Φ $(sum_tmul_tmul_eq 𝓡 𝓡₁ 𝓡₂))
  simp only [map_sum, hΦ] at key
  have lhs_eq : ∑ i ∈ 𝓡.index, ∑ k ∈ (𝓡₁ i).index,
        f (𝓡.right i * (c * antipode R ((𝓡₁ i).right k))) * m (d * antipode R ((𝓡₁ i).left k))
      = ∑ i ∈ 𝓡.index, ∑ k ∈ (𝓡₁ i).index,
        m (d * antipode R ((𝓡₁ i).left k)) * f (antipode R ((𝓡₁ i).right k) * 𝓡.right i * c) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (f _)]; congr 2; ring
  rw [lhs_eq, key]
  have inner : ∀ i ∈ 𝓡.index, ∑ k ∈ (𝓡₂ i).index,
        m (d * antipode R (𝓡.left i)) * f (antipode R ((𝓡₂ i).left k) * (𝓡₂ i).right k * c)
      = Coalgebra.counit (R := R) (𝓡.right i) * (m (d * antipode R (𝓡.left i)) * f c) := by
    intro i _
    rw [← Finset.mul_sum]
    have h1 : ∑ k ∈ (𝓡₂ i).index, f (antipode R ((𝓡₂ i).left k) * (𝓡₂ i).right k * c)
        = f ((∑ k ∈ (𝓡₂ i).index, antipode R ((𝓡₂ i).left k) * (𝓡₂ i).right k) * c) := by
      rw [Finset.sum_mul, map_sum]
    rw [h1, sum_antipode_mul_eq_smul (𝓡₂ i), smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl inner]
  have h3 : m (d * antipode R
      (∑ i ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.right i) • 𝓡.left i)) * f c
      = ∑ i ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.right i) * (m (d * antipode R (𝓡.left i))
          * f c) := by
    rw [map_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul]; ring
  have h4 : ∑ i ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.right i) • 𝓡.left i = b := by
    simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using
      congr(TensorProduct.rid R B $(sum_tmul_counit_eq (R := R) 𝓡))
  rw [← h3, h4, mul_comm]

omit [Module.Finite R B] in
omit [Module.Free R B] in
private theorem dconv_smul (f m : Module.Dual R B) (b : B) {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr R b ι𝓡) :
    dconv f (b • m)
      = ∑ i ∈ 𝓡.index, 𝓡.left i • dconv (f ∘ₗ LinearMap.mulLeft R (𝓡.right i)) m := by
  ext x
  set 𝓧 := ℛ R x
  rw [dconv_apply_repr _ _ 𝓧, LinearMap.sum_apply]
  simp only [dual_smul_apply]
  let 𝓡₁ := fun (i : ι𝓡) => ℛ R (𝓡.left i)
  have hrep : ∀ i ∈ 𝓡.index,
      dconv (f ∘ₗ LinearMap.mulLeft R (𝓡.right i)) m (x * antipode R (𝓡.left i))
        = ∑ j ∈ 𝓧.index, ∑ k ∈ (𝓡₁ i).index,
            f (𝓡.right i * (𝓧.left j * antipode R ((𝓡₁ i).right k)))
              * m (𝓧.right j * antipode R ((𝓡₁ i).left k)) := by
    intro i _
    have hΔ : Coalgebra.comul (R := R) (x * antipode R (𝓡.left i))
        = ∑ j ∈ 𝓧.index, ∑ k ∈ (𝓡₁ i).index,
            (𝓧.left j * antipode R ((𝓡₁ i).right k))
              ⊗ₜ[R] (𝓧.right j * antipode R ((𝓡₁ i).left k)) := by
      rw [Bialgebra.comul_mul, HopfKerHopf.comul_antipode_eq_sum (𝓡₁ i), ← 𝓧.eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [dconv, LinearMap.coe_comp, Function.comp_apply, hΔ, map_sum,
      TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.mulLeft_apply]
  rw [Finset.sum_congr rfl hrep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (compat_core f m b (𝓧.left j) (𝓧.right j) 𝓡 𝓡₁).symm

private theorem dualCoaction_compat :
    dualCoaction ∘ₗ RightHopfModule.hsmul (k := R) (H := B) (M := Module.Dual R B)
      = TensorProduct.map (RightHopfModule.hsmul (k := R)) (LinearMap.mul' R B)
          ∘ₗ (TensorProduct.tensorTensorTensorComm R B B (Module.Dual R B) B).toLinearMap
          ∘ₗ TensorProduct.map (Coalgebra.comul (R := R) (A := B)) dualCoaction := by
  refine TensorProduct.ext' fun b m => ?_
  set 𝓡 := ℛ R b
  simp only [LinearMap.coe_comp, Function.comp_apply, RightHopfModule.hsmul_tmul,
    TensorProduct.map_tmul, dualCoaction_apply]
  conv_rhs => rw [← 𝓡.eq]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum]
  simp only [LinearEquiv.coe_coe, TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    RightHopfModule.hsmul_tmul, LinearMap.mul'_apply]
  have hexp : ∀ i j, (𝓡.left i • dconv ((bB (R := R) (B := B)).coord j) m) ⊗ₜ[R] (𝓡.right i * bB j)
      = ∑ l, ((bB (R := R) (B := B)).coord l (𝓡.right i * bB j)
          • (𝓡.left i • dconv ((bB (R := R) (B := B)).coord j) m)) ⊗ₜ[R] bB l :=
    fun i j => tmul_eq_sum_coord _ _
  simp_rw [hexp]
  conv_rhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ ?_
  intro l
  simp_rw [← TensorProduct.sum_tmul]
  congr 1
  rw [dconv_smul _ _ _ 𝓡, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hx : ∀ j, ((bB (R := R) (B := B)).coord l (𝓡.right i * bB j))
        • (𝓡.left i • dconv ((bB (R := R) (B := B)).coord j) m)
      = 𝓡.left i • ((((bB (R := R) (B := B)).coord l ∘ₗ LinearMap.mulLeft R (𝓡.right i)) (bB j))
          • dconv ((bB (R := R) (B := B)).coord j) m) := by
    intro j; rw [smul_comm]; rfl
  simp_rw [hx, ← Finset.smul_sum, sum_apply_smul_dconv_coord]

private theorem dual_rightHopfModule :
    RightHopfModule (k := R) (H := B) (dualCoaction (R := R) (B := B)) :=
  ⟨dualCoaction_counit, dualCoaction_coassoc, dualCoaction_compat⟩

private theorem integral_of_mem_coinvariants {Λ : Module.Dual R B}
    (hΛ : Λ ∈ RightComodule.coinvariants (k := R) (H := B)
        (dualCoaction (R := R) (B := B))) (b : B) :
    (TensorProduct.rid R B) (Λ.lTensor B (Coalgebra.comul (R := R) b)) = (Λ b) • (1 : B) := by
  rw [RightComodule.mem_coinvariants, dualCoaction_apply] at hΛ
  have hconv : ∀ f : Module.Dual R B, dconv f Λ = f 1 • Λ := by
    intro f
    have := congr((TensorProduct.rid R (Module.Dual R B)) (f.lTensor (Module.Dual R B) $hΛ))
    simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      sum_apply_smul_dconv_coord] using this
  set 𝓡 := ℛ R b
  have lhs : (TensorProduct.rid R B) (Λ.lTensor B (Coalgebra.comul (R := R) b))
      = ∑ i ∈ 𝓡.index, Λ (𝓡.right i) • 𝓡.left i := by
    rw [← 𝓡.eq]; simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rw [lhs]
  refine (bB (R := R) (B := B)).ext_elem fun l => ?_
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, ← Module.Basis.coord_apply]
  have h1 : ∑ i ∈ 𝓡.index, Λ (𝓡.right i) * (bB (R := R) (B := B)).coord l (𝓡.left i)
      = dconv ((bB (R := R) (B := B)).coord l) Λ b := by
    rw [dconv_apply_repr _ _ 𝓡]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, hconv, LinearMap.smul_apply, smul_eq_mul, mul_comm]

private theorem exists_frobenius_integrals :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) •
          (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b := by
  classical
  have RH := dual_rightHopfModule (R := R) (B := B)
  set z := RH.invActMap (Coalgebra.counit : Module.Dual R B) with hz_def
  have hz : RightComodule.actMap _ z = (Coalgebra.counit : Module.Dual R B) := RH.actMap_invActMap _
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  refine ⟨s.card, fun j => ((s.equivFin.symm j).1.1 : Module.Dual R B),
    fun j => antipode R (s.equivFin.symm j).1.2, ?_, ?_⟩
  · intro j b
    exact integral_of_mem_coinvariants (s.equivFin.symm j).1.1.2 b
  · intro b
    have happ := congr($hz b)
    rw [hs, map_sum, LinearMap.sum_apply] at happ
    simp only [RightComodule.actMap_tmul, dual_smul_apply] at happ
    rw [← happ, ← Finset.sum_coe_sort s]
    rw [← Fintype.sum_equiv s.equivFin.symm _ _ (fun _ => rfl)]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [mul_comm]

end DualHopfModule


end HopfAlgebra.LeftIntegral

open HopfAlgebra.LeftIntegral in
/-- **Left integrals on a finite free Hopf algebra.** Let `R` be a commutative ring and `B` a
commutative Hopf algebra over `R` that is finite and free as an `R`-module. There are finitely
many linear forms `Λ j : B → R` that are left integrals, `(id ⊗ Λ j) (Δ b) = Λ j b • 1` for every
`b : B`, and elements `u j : B` with `∑ j, Λ j (u j * b) = ε b` for every `b : B`. -/
theorem HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit {R : Type u} [CommRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) •
          (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b :=
  exists_frobenius_integrals
