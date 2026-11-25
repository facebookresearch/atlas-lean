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

public import MathlibExt.LinearAlgebra.TensorProduct.DirectLimit.Diagonal
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Native finite-factor decompositions for diagonal module colimits

The finite tensor coordinate is the existing PiTensorProduct, with the native
sum-type decomposition and reindexing. No tensor model is defined here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe r v

namespace PiTensorProduct

variable (R : Type r) [CommSemiring R]

/-- Split the last factor of the actual dependent finite pi tensor product. -/
def finSnocEquiv (n : ℕ) (V : Fin (n + 1) → Type v)
    [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] :
    (⨂[R] j : Fin (n + 1), V j) ≃ₗ[R]
      (⨂[R] j : Fin n, V j.castSucc) ⊗[R] V (Fin.last n) :=
  (reindex R V (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm).trans
    ((tmulEquivDep R
        (fun j : Fin n ⊕ Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
        (subsingletonEquiv (R := R)
          (s := fun j : Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)))

/-- The native split retains the original prefix order and actual last entry. -/
@[simp]
theorem finSnocEquiv_tprod (n : ℕ) (V : Fin (n + 1) → Type v)
    [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] (x : ∀ j, V j) :
    finSnocEquiv R n V (tprod R x) =
      tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R] x (Fin.last n) := by
  rw [finSnocEquiv, LinearEquiv.trans_apply, reindex_tprod]
  change TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
      (subsingletonEquiv (R := R)
        (s := fun j : Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)
      ((tmulEquivDep R
        (fun j : Fin n ⊕ Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j))).symm
        (tprod R (fun j => x ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j)))) = _
  rw [tmulEquivDep_symm_apply]
  change TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
      (subsingletonEquiv (R := R)
        (s := fun j : Fin 1 =>
          V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)
      (tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R]
        tprod R (fun j : Fin 1 =>
          x ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j)))) =
    tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R] x (Fin.last n)
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    subsingletonEquiv_apply_tprod]
  rfl

end PiTensorProduct

universe i m n b

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {β : Type b}
  {M : ι → Type m} [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
  {V : β → ι → Type n} [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)]
  (f : ∀ a c, a ≤ c → M a →ₗ[R] M c)
  (g : ∀ j a c, a ≤ c → V j a →ₗ[R] V j c)

/-- The simultaneous transition preserves the coefficient and every actual
finite-factor tensor map; the factor family may be dependent. -/
def finiteDiagonalTransition (a c : ι) (h : a ≤ c) :
    M a ⊗[R] (⨂[R] j : β, V j a) →ₗ[R] M c ⊗[R] (⨂[R] j : β, V j c) :=
  TensorProduct.map (f a c h) (PiTensorProduct.map (fun j => g j a c h))

/-- The actual simultaneous finite tensor stage module quotient. -/
abbrev finiteDiagonalLimit :=
  Module.DirectLimit (fun a => M a ⊗[R] (⨂[R] j : β, V j a)) (finiteDiagonalTransition f g)

/-- The canonical comparison uses native of maps in the coefficient and
each dependent factor, rather than a caller-supplied comparison. -/
def finiteDiagonalToTensor :
    finiteDiagonalLimit f g →ₗ[R]
      Module.DirectLimit M f ⊗[R] (⨂[R] j : β, Module.DirectLimit (V j) (g j)) :=
  Module.DirectLimit.lift R ι
    (fun a => M a ⊗[R] (⨂[R] j : β, V j a)) (finiteDiagonalTransition f g)
    (fun a => TensorProduct.map (Module.DirectLimit.of R ι M f a)
      (PiTensorProduct.map (fun j => Module.DirectLimit.of R ι (V j) (g j) a))) (by
      intro a c h z
      have he :
          (TensorProduct.map (Module.DirectLimit.of R ι M f c)
            (PiTensorProduct.map (fun j => Module.DirectLimit.of R ι (V j) (g j) c))).comp
              (finiteDiagonalTransition f g a c h) =
            TensorProduct.map (Module.DirectLimit.of R ι M f a)
              (PiTensorProduct.map (fun j => Module.DirectLimit.of R ι (V j) (g j) a)) := by
        apply TensorProduct.ext'
        intro x q
        have hq :
            TensorProduct.curry
                ((TensorProduct.map (Module.DirectLimit.of R ι M f c)
                  (PiTensorProduct.map
                    (fun j => Module.DirectLimit.of R ι (V j) (g j) c))).comp
                    (finiteDiagonalTransition f g a c h)) x =
              TensorProduct.curry
                (TensorProduct.map (Module.DirectLimit.of R ι M f a)
                  (PiTensorProduct.map
                    (fun j => Module.DirectLimit.of R ι (V j) (g j) a))) x := by
          apply PiTensorProduct.ext
          apply MultilinearMap.ext
          intro y
          simp only [LinearMap.compMultilinearMap_apply, TensorProduct.curry_apply,
            LinearMap.comp_apply,
            finiteDiagonalTransition, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
            Module.DirectLimit.of_f]
        exact LinearMap.congr_fun hq q
      exact LinearMap.congr_fun he z)

/-- The comparison's generator characteristic retains the original coefficient
position and each actual factor-stage injection. -/
@[simp]
theorem finiteDiagonalToTensor_of_tprod (a : ι) (x : M a) (y : ∀ j : β, V j a) :
    finiteDiagonalToTensor f g
        (Module.DirectLimit.of R ι
          (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
          (finiteDiagonalTransition f g) a (x ⊗ₜ[R] PiTensorProduct.tprod R y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
        PiTensorProduct.tprod R
          (fun j => Module.DirectLimit.of R ι (V j) (g j) a (y j)) := by
  simp only [finiteDiagonalToTensor, Module.DirectLimit.lift_of,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod]

omit [DecidableEq ι] in
/-- Genuine coefficient and factor transition systems induce the simultaneous
finite tensor transition system. This is a proved structural property of the
existing tensor maps, with no injectivity assumption. -/
theorem finiteDiagonalTransition_directedSystem
    [DirectedSystem M (f · · ·)] [∀ j, DirectedSystem (V j) (g j · · ·)] :
    DirectedSystem (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
      (finiteDiagonalTransition f g · · ·) where
  map_self := by
    intro a z
    have hf : f a a le_rfl = (LinearMap.id : M a →ₗ[R] M a) :=
      LinearMap.ext (fun x : M a => DirectedSystem.map_self' f (i := a) x)
    have hg :
        (fun j => g j a a le_rfl) =
          (fun j => (LinearMap.id : V j a →ₗ[R] V j a)) := by
      funext j
      exact LinearMap.ext (fun x : V j a => DirectedSystem.map_self' (g j) (i := a) x)
    simp only [finiteDiagonalTransition, hf, hg, PiTensorProduct.map_id,
      TensorProduct.map_id, LinearMap.id_apply]
  map_map := by
    intro c b a hab hbc z
    have hf :
        (f b c hbc).comp (f a b hab) = f a c (hab.trans hbc) :=
      LinearMap.ext (DirectedSystem.map_map' f hab hbc)
    have hg :
        (fun j => (g j b c hbc).comp (g j a b hab)) =
          (fun j => g j a c (hab.trans hbc)) := by
      funext j
      exact LinearMap.ext (DirectedSystem.map_map' (g j) hab hbc)
    have he :
        (finiteDiagonalTransition f g b c hbc).comp
            (finiteDiagonalTransition f g a b hab) =
          finiteDiagonalTransition f g a c (hab.trans hbc) := by
      dsimp only [finiteDiagonalTransition]
      rw [← TensorProduct.map_comp, ← PiTensorProduct.map_comp, hf, hg]
    exact LinearMap.congr_fun he z

end TensorProduct

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {M : ι → Type m} [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]

/-- Native tensor unit identification for a zero-factor stage. -/
def finiteEmptyStageEquiv (V : Fin 0 → ι → Type n)
    [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)] (a : ι) :
    M a ⊗[R] (⨂[R] j : Fin 0, V j a) ≃ₗ[R] M a :=
  (TensorProduct.congr (LinearEquiv.refl R (M a))
    (PiTensorProduct.isEmptyEquiv (R := R) (s := fun j => V j a) (Fin 0))).trans
      (TensorProduct.rid R (M a))

omit [Preorder ι] [DecidableEq ι] in
@[simp]
theorem finiteEmptyStageEquiv_tprod (V : Fin 0 → ι → Type n)
    [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)]
    (a : ι) (x : M a) (y : ∀ j, V j a) :
    finiteEmptyStageEquiv (R := R) (M := M) V a
        (x ⊗ₜ[R] PiTensorProduct.tprod R y) = x := by
  simp only [finiteEmptyStageEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

/-- The actual last-factor decomposition with the original coefficient in
the first position. Only native tensor associativity and finite reindexing
are used. -/
def finiteSnocStageEquiv (t : ℕ) (V : Fin (t + 1) → ι → Type n)
    [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)] (a : ι) :
    M a ⊗[R] (⨂[R] j : Fin (t + 1), V j a) ≃ₗ[R]
      (M a ⊗[R] (⨂[R] j : Fin t, V j.castSucc a)) ⊗[R] V (Fin.last t) a :=
  (TensorProduct.congr (LinearEquiv.refl R (M a))
      (PiTensorProduct.finSnocEquiv R t (fun j => V j a))).trans
    (TensorProduct.assoc R (M a) (⨂[R] j : Fin t, V j.castSucc a)
      (V (Fin.last t) a)).symm

omit [Preorder ι] [DecidableEq ι] in
@[simp]
theorem finiteSnocStageEquiv_tprod (t : ℕ) (V : Fin (t + 1) → ι → Type n)
    [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)]
    (a : ι) (x : M a) (y : ∀ j, V j a) :
    finiteSnocStageEquiv (R := R) (M := M) t V a
        (x ⊗ₜ[R] PiTensorProduct.tprod R y) =
      (x ⊗ₜ[R] PiTensorProduct.tprod R (fun j : Fin t => y j.castSucc)) ⊗ₜ[R]
        y (Fin.last t) := by
  simp only [finiteSnocStageEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.finSnocEquiv_tprod, TensorProduct.assoc_symm_tmul]

end TensorProduct

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {M : ι → Type m} [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
  (f : ∀ a c, a ≤ c → M a →ₗ[R] M c)
  [DirectedSystem M (f · · ·)] [IsDirectedOrder ι]

/-- The finite induction constructs an actual equivalence with the prescribed
stage characteristic. It is used only to prove bijectivity of the canonical
forward map; no comparison is requested as caller data. -/
private theorem exists_finiteDiagonalEquiv_fin (t : ℕ) :
    ∀ (V : Fin t → ι → Type n)
      [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)]
      (g : ∀ j a c, a ≤ c → V j a →ₗ[R] V j c)
      [∀ j, DirectedSystem (V j) (g j · · ·)],
      ∃ e : finiteDiagonalLimit f g ≃ₗ[R]
          Module.DirectLimit M f ⊗[R]
            (⨂[R] j : Fin t, Module.DirectLimit (V j) (g j)),
        ∀ (a : ι) (x : M a) (y : ∀ j, V j a),
          e (Module.DirectLimit.of R ι
            (fun a => M a ⊗[R] (⨂[R] j : Fin t, V j a))
            (finiteDiagonalTransition f g) a
              (x ⊗ₜ[R] PiTensorProduct.tprod R y)) =
          Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
            PiTensorProduct.tprod R
              (fun j => Module.DirectLimit.of R ι (V j) (g j) a (y j)) := by
  induction t with
  | zero =>
    intro V hAdd hModule g hDS
    let e₀ := fun a => finiteEmptyStageEquiv (R := R) (M := M) V a
    have h₀ :
        ∀ a c h, (e₀ c).toLinearMap.comp (finiteDiagonalTransition f g a c h) =
          (f a c h).comp (e₀ a).toLinearMap := by
      intro a c h
      apply TensorProduct.ext'
      intro x z
      have he :
          TensorProduct.curry
              ((e₀ c).toLinearMap.comp (finiteDiagonalTransition f g a c h)) x =
            TensorProduct.curry ((f a c h).comp (e₀ a).toLinearMap) x := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [LinearMap.compMultilinearMap_apply, TensorProduct.curry_apply,
          LinearMap.comp_apply, finiteDiagonalTransition, TensorProduct.map_tmul,
          PiTensorProduct.map_tprod]
        change finiteEmptyStageEquiv (R := R) (M := M) V c
            ((f a c h) x ⊗ₜ[R] PiTensorProduct.tprod R
              (fun j : Fin 0 => g j a c h (y j))) =
          f a c h
            (finiteEmptyStageEquiv (R := R) (M := M) V a
              (x ⊗ₜ[R] PiTensorProduct.tprod R y))
        rw [finiteEmptyStageEquiv_tprod, finiteEmptyStageEquiv_tprod]
      exact LinearMap.congr_fun he z
    let eT :
        Module.DirectLimit M f ⊗[R]
            (⨂[R] j : Fin 0, Module.DirectLimit (V j) (g j)) ≃ₗ[R]
          Module.DirectLimit M f :=
      (TensorProduct.congr (LinearEquiv.refl R (Module.DirectLimit M f))
        (PiTensorProduct.isEmptyEquiv (R := R)
          (s := fun j => Module.DirectLimit (V j) (g j)) (Fin 0))).trans
        (TensorProduct.rid R (Module.DirectLimit M f))
    refine ⟨(Module.DirectLimit.congr e₀ h₀).trans eT.symm, ?_⟩
    intro a x y
    apply eT.injective
    change eT
        (eT.symm ((Module.DirectLimit.congr e₀ h₀)
          (Module.DirectLimit.of R ι
            (fun a => M a ⊗[R] (⨂[R] j : Fin 0, V j a))
            (finiteDiagonalTransition f g) a
            (x ⊗ₜ[R] PiTensorProduct.tprod R y)))) =
      eT (Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
        PiTensorProduct.tprod R
          (fun j : Fin 0 => Module.DirectLimit.of R ι (V j) (g j) a (y j)))
    rw [LinearEquiv.apply_symm_apply, Module.DirectLimit.congr_apply_of]
    simp only [e₀, finiteEmptyStageEquiv_tprod, eT, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]
  | succ t ih =>
    intro V hAdd hModule g hDS
    let VP : Fin t → ι → Type n := fun j a => V j.castSucc a
    let gP : ∀ j a c, a ≤ c → VP j a →ₗ[R] VP j c :=
      fun j a c h => g j.castSucc a c h
    let : ∀ j, DirectedSystem (VP j) (gP j · · ·) :=
      fun j => hDS j.castSucc
    obtain ⟨eP, hP⟩ := ih VP gP
    let W := fun a => M a ⊗[R] (⨂[R] j : Fin t, VP j a)
    let fP : ∀ a c, a ≤ c → W a →ₗ[R] W c := finiteDiagonalTransition f gP
    let : DirectedSystem W (fP · · ·) :=
      finiteDiagonalTransition_directedSystem f gP
    let eS := fun a => finiteSnocStageEquiv (R := R) (M := M) t V a
    have hS :
        ∀ a c h, (eS c).toLinearMap.comp (finiteDiagonalTransition f g a c h) =
          (diagonalTransition fP (g (Fin.last t)) a c h).comp
            (eS a).toLinearMap := by
      intro a c h
      apply TensorProduct.ext'
      intro x z
      have he :
          TensorProduct.curry
              ((eS c).toLinearMap.comp (finiteDiagonalTransition f g a c h)) x =
            TensorProduct.curry
              ((diagonalTransition fP (g (Fin.last t)) a c h).comp
                (eS a).toLinearMap) x := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [LinearMap.compMultilinearMap_apply, TensorProduct.curry_apply,
          LinearMap.comp_apply, finiteDiagonalTransition, TensorProduct.map_tmul,
          PiTensorProduct.map_tprod]
        change finiteSnocStageEquiv (R := R) (M := M) t V c
            ((f a c h) x ⊗ₜ[R] PiTensorProduct.tprod R
              (fun j : Fin (t + 1) => g j a c h (y j))) =
          TensorProduct.map
            (TensorProduct.map (f a c h)
              (PiTensorProduct.map (fun j : Fin t => g j.castSucc a c h)))
            (g (Fin.last t) a c h)
            (finiteSnocStageEquiv (R := R) (M := M) t V a
              (x ⊗ₜ[R] PiTensorProduct.tprod R y))
        simp only [finiteSnocStageEquiv_tprod, TensorProduct.map_tmul,
          PiTensorProduct.map_tprod]
      exact LinearMap.congr_fun he z
    let eL := Module.DirectLimit.congr eS hS
    let eB := directLimitDiagonal fP (g (Fin.last t))
    let eT :
        ((Module.DirectLimit M f ⊗[R]
          (⨂[R] j : Fin t, Module.DirectLimit (VP j) (gP j))) ⊗[R]
            Module.DirectLimit (V (Fin.last t)) (g (Fin.last t))) ≃ₗ[R]
          Module.DirectLimit M f ⊗[R]
            (⨂[R] j : Fin (t + 1), Module.DirectLimit (V j) (g j)) :=
      (TensorProduct.assoc R (Module.DirectLimit M f)
        (⨂[R] j : Fin t, Module.DirectLimit (VP j) (gP j))
        (Module.DirectLimit (V (Fin.last t)) (g (Fin.last t)))).trans
          (TensorProduct.congr (LinearEquiv.refl R (Module.DirectLimit M f))
            (PiTensorProduct.finSnocEquiv R t
              (fun j => Module.DirectLimit (V j) (g j))).symm)
    refine ⟨eL.trans
      (eB.trans ((TensorProduct.congr eP
        (LinearEquiv.refl R
          (Module.DirectLimit (V (Fin.last t)) (g (Fin.last t))))).trans eT)), ?_⟩
    intro a x y
    change eT
      (TensorProduct.congr eP
        (LinearEquiv.refl R (Module.DirectLimit (V (Fin.last t)) (g (Fin.last t))))
          (eB (eL (Module.DirectLimit.of R ι
            (fun a => M a ⊗[R] (⨂[R] j : Fin (t + 1), V j a))
              (finiteDiagonalTransition f g) a
                (x ⊗ₜ[R] PiTensorProduct.tprod R y))))) = _
    dsimp only [eL]
    rw [Module.DirectLimit.congr_apply_of]
    simp only [eS, finiteSnocStageEquiv_tprod]
    dsimp only [eB]
    rw [directLimitDiagonal_of_tmul]
    simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [hP]
    dsimp only [eT]
    rw [LinearEquiv.trans_apply, TensorProduct.assoc_tmul]
    apply (TensorProduct.congr (LinearEquiv.refl R (Module.DirectLimit M f))
      (PiTensorProduct.finSnocEquiv R t
        (fun j => Module.DirectLimit (V j) (g j)))).injective
    simp only [LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, PiTensorProduct.finSnocEquiv_tprod]
    rfl

end TensorProduct

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {β : Type b} [Finite β]
  {M : ι → Type m} [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
  {V : β → ι → Type n} [∀ j a, AddCommMonoid (V j a)] [∀ j a, Module R (V j a)]
  (f : ∀ a c, a ≤ c → M a →ₗ[R] M c)
  (g : ∀ j a c, a ≤ c → V j a →ₗ[R] V j c)
  [DirectedSystem M (f · · ·)] [∀ j, DirectedSystem (V j) (g j · · ·)]
  [IsDirectedOrder ι]

/-- Transport the earned finite induction by the native equivalence between
a finite index and Fin(card β). Both the stage and target transports are
the actual native pi-tensor reindexing. -/
private theorem exists_finiteDiagonalEquiv :
    ∃ e : finiteDiagonalLimit f g ≃ₗ[R]
        Module.DirectLimit M f ⊗[R]
          (⨂[R] j : β, Module.DirectLimit (V j) (g j)),
      ∀ (a : ι) (x : M a) (y : ∀ j, V j a),
        e (Module.DirectLimit.of R ι
          (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
          (finiteDiagonalTransition f g) a
            (x ⊗ₜ[R] PiTensorProduct.tprod R y)) =
        Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
          PiTensorProduct.tprod R
            (fun j => Module.DirectLimit.of R ι (V j) (g j) a (y j)) := by
  classical
  let := Fintype.ofFinite β
  let eI := Fintype.equivFin β
  let VF : Fin (Fintype.card β) → ι → Type n := fun j a => V (eI.symm j) a
  let gF : ∀ j a c, a ≤ c → VF j a →ₗ[R] VF j c :=
    fun j a c h => g (eI.symm j) a c h
  let : ∀ j, DirectedSystem (VF j) (gF j · · ·) :=
    fun j => inferInstanceAs (DirectedSystem (V (eI.symm j)) (g (eI.symm j) · · ·))
  obtain ⟨eF, hF⟩ := exists_finiteDiagonalEquiv_fin f (Fintype.card β) VF gF
  let eS := fun a => TensorProduct.congr (LinearEquiv.refl R (M a))
    (PiTensorProduct.reindex R (fun j => V j a) eI)
  have hS :
      ∀ a c h, (eS c).toLinearMap.comp (finiteDiagonalTransition f g a c h) =
        (finiteDiagonalTransition f gF a c h).comp (eS a).toLinearMap := by
    intro a c h
    apply TensorProduct.ext'
    intro x z
    have he :
        TensorProduct.curry
            ((eS c).toLinearMap.comp (finiteDiagonalTransition f g a c h)) x =
          TensorProduct.curry
            ((finiteDiagonalTransition f gF a c h).comp (eS a).toLinearMap) x := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp only [LinearMap.compMultilinearMap_apply, TensorProduct.curry_apply,
        LinearMap.comp_apply, finiteDiagonalTransition, TensorProduct.map_tmul,
        PiTensorProduct.map_tprod]
      change (TensorProduct.congr (LinearEquiv.refl R (M c))
          (PiTensorProduct.reindex R (fun j : β => V j c) eI))
          ((f a c h) x ⊗ₜ[R] PiTensorProduct.tprod R
            (fun j : β => g j a c h (y j))) =
        TensorProduct.map (f a c h)
          (PiTensorProduct.map
            (fun j : Fin (Fintype.card β) => g (eI.symm j) a c h))
          ((TensorProduct.congr (LinearEquiv.refl R (M a))
            (PiTensorProduct.reindex R (fun j : β => V j a) eI))
            (x ⊗ₜ[R] PiTensorProduct.tprod R y))
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        PiTensorProduct.reindex_tprod, TensorProduct.map_tmul,
        PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun he z
  let eT := TensorProduct.congr (LinearEquiv.refl R (Module.DirectLimit M f))
    (PiTensorProduct.reindex R (fun j => Module.DirectLimit (V j) (g j)) eI)
  refine ⟨(Module.DirectLimit.congr eS hS).trans (eF.trans eT.symm), ?_⟩
  intro a x y
  apply eT.injective
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, Module.DirectLimit.congr_apply_of]
  simp only [eS, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.reindex_tprod]
  rw [hF]
  simp only [eT, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.reindex_tprod, VF, gF]

/-- The canonical simultaneous-stage map is bijective for a genuinely finite
factor family and directed transition systems. The proof constructs its inverse;
no injective transitions or comparison is assumed. -/
theorem finiteDiagonalToTensor_bijective :
    Function.Bijective (finiteDiagonalToTensor f g) := by
  obtain ⟨e, he⟩ := exists_finiteDiagonalEquiv f g
  have hf : finiteDiagonalToTensor f g = e.toLinearMap := by
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι)
      (G := fun a => M a ⊗[R] (⨂[R] j : β, V j a))
      (f := finiteDiagonalTransition f g)
    intro a
    apply TensorProduct.ext'
    intro x z
    have hz :
        TensorProduct.curry
            ((finiteDiagonalToTensor f g).comp
              (Module.DirectLimit.of R ι
                (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
                (finiteDiagonalTransition f g) a)) x =
          TensorProduct.curry
            (e.toLinearMap.comp
              (Module.DirectLimit.of R ι
                (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
                (finiteDiagonalTransition f g) a)) x := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      change finiteDiagonalToTensor f g
          (Module.DirectLimit.of R ι
            (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
            (finiteDiagonalTransition f g) a
              (x ⊗ₜ[R] PiTensorProduct.tprod R y)) =
        e (Module.DirectLimit.of R ι
          (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
          (finiteDiagonalTransition f g) a
            (x ⊗ₜ[R] PiTensorProduct.tprod R y))
      exact (finiteDiagonalToTensor_of_tprod f g a x y).trans (he a x y).symm
    exact LinearMap.congr_fun hz z
  rw [hf]
  exact e.bijective

/-- The finite tensor/direct-limit diagonal comparison has the exact canonical
native lift as its forward map. Scalar, index, coefficient and factor worlds
are independent, and an empty factor family is allowed. -/
def directLimitFinite :
    finiteDiagonalLimit f g ≃ₗ[R]
      Module.DirectLimit M f ⊗[R]
        (⨂[R] j : β, Module.DirectLimit (V j) (g j)) :=
  LinearEquiv.ofBijective (finiteDiagonalToTensor f g)
    (finiteDiagonalToTensor_bijective f g)

/-- The forward generator formula retains the original coefficient position
and every actual simultaneous factor-stage map. -/
@[simp]
theorem directLimitFinite_of_tprod (a : ι) (x : M a) (y : ∀ j, V j a) :
    directLimitFinite f g
        (Module.DirectLimit.of R ι
          (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
          (finiteDiagonalTransition f g) a
            (x ⊗ₜ[R] PiTensorProduct.tprod R y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
        PiTensorProduct.tprod R
          (fun j => Module.DirectLimit.of R ι (V j) (g j) a (y j)) :=
  finiteDiagonalToTensor_of_tprod f g a x y

/-- The inverse sends a simultaneous family of actual stage classes to its
original module-colimit class. -/
@[simp]
theorem directLimitFinite_symm_of_tprod (a : ι) (x : M a) (y : ∀ j, V j a) :
    (directLimitFinite f g).symm
        (Module.DirectLimit.of R ι M f a x ⊗ₜ[R]
          PiTensorProduct.tprod R
            (fun j => Module.DirectLimit.of R ι (V j) (g j) a (y j))) =
      Module.DirectLimit.of R ι
        (fun a => M a ⊗[R] (⨂[R] j : β, V j a))
        (finiteDiagonalTransition f g) a
          (x ⊗ₜ[R] PiTensorProduct.tprod R y) := by
  rw [← directLimitFinite_of_tprod f g a x y, LinearEquiv.symm_apply_apply]

end TensorProduct
