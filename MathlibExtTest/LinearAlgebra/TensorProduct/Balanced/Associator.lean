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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import Mathlib.Algebra.Module.NatInt

/-! Independent-world callers use the actual association maps and old unitors.
Original coefficient actions are inputs; nested tensor actions and inverse
or coherence laws are constructed by the shared API. -/

@[expose] public section

noncomputable section

open MulOpposite

universe u vS vR vM vN vP vM' vN' vP' vQ vT

namespace TensorProduct.Balanced.AssociatorPublicApi

variable (k : Type u) (S : Type vS) (R : Type vR)
  (M : Type vM) (N : Type vN) (P : Type vP)
  [CommRing k] [Semiring S] [Semiring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module Sᵐᵒᵖ M] [Module S N] [Module Rᵐᵒᵖ N] [Module R P]
  [SMulCommClass S k N] [SMulCommClass Rᵐᵒᵖ k N]
  [SMulCommClass S Rᵐᵒᵖ N]

example : assocSource k S R M N P ≃ₗ[k] assocTarget k S R M N P :=
  assoc k S R M N P

example (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    assoc k S R M N P
        (mk k R (Balanced k S M N) P (mk k S M N m n) p) =
      mk k S M (Balanced k R N P) m (mk k R N P n p) :=
  assoc_mk_mk k S R M N P m n p

example (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    (assoc k S R M N P).symm
        (mk k S M (Balanced k R N P) m (mk k R N P n p)) =
      mk k R (Balanced k S M N) P (mk k S M N m n) p :=
  assoc_symm_mk_mk k S R M N P m n p

example (x : assocSource k S R M N P) :
    (assoc k S R M N P).symm (assoc k S R M N P x) = x :=
  (assoc k S R M N P).symm_apply_apply x

example {M' : Type vM'} {N' : Type vN'} {P' : Type vP'}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module k M'] [Module k N'] [Module k P']
    [Module Sᵐᵒᵖ M'] [Module S N'] [Module Rᵐᵒᵖ N'] [Module R P']
    [SMulCommClass S k N'] [SMulCommClass Rᵐᵒᵖ k N']
    [SMulCommClass S Rᵐᵒᵖ N']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N') (h : P →ₗ[k] P')
    (fS : ∀ (s : S) (m : M), f (op s • m) = op s • f m)
    (gS : ∀ (s : S) (n : N), g (s • n) = s • g n)
    (gR : ∀ (t : Rᵐᵒᵖ) (n : N), g (t • n) = t • g n)
    (hR : ∀ (r : R) (p : P), h (r • p) = r • h p) :
    (assocHom k S R M' N' P').comp (mapAssocSource f g h fS gS gR hR) =
      (mapAssocTarget f g h fS gS gR hR).comp (assocHom k S R M N P) :=
  assocHom_naturality f g h fS gS gR hR

example (Q : Type vQ) [Semiring Q] [Module Q M]
    [SMulCommClass Q k M] [SMulCommClass Q Sᵐᵒᵖ M]
    (q : Q) (x : assocSource k S R M N P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := leftModule k S Q M N
    letI := leftSMulCommClass k S Q M N
    letI := leftRightSMulCommClass k S R M N Q
    letI := leftModule k R Q (Balanced k S M N) P
    letI := leftModule k S Q M (Balanced k R N P)
    assoc k S R M N P (q • x) = q • assoc k S R M N P x :=
  assoc_left_smul k S R M N P Q q x

example (T : Type vT) [Semiring T] [Module Tᵐᵒᵖ P]
    [SMulCommClass Tᵐᵒᵖ k P] [SMulCommClass R Tᵐᵒᵖ P]
    (t : Tᵐᵒᵖ) (x : assocSource k S R M N P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := rightModule k R T N P
    letI := rightSMulCommClass k R T N P
    letI := leftRightSMulCommClass_of_factor_actions k R S T N P
    letI := rightModule k R T (Balanced k S M N) P
    letI := rightModule k S T M (Balanced k R N P)
    assoc k S R M N P (t • x) = t • assoc k S R M N P x :=
  assoc_right_smul k S R M N P T t x

/-- Integer ground needs no additional ground-algebra or ground-action input. -/
example (S₀ : Type vS) (R₀ : Type vR) [Semiring S₀] [Semiring R₀]
    (M₀ : Type vM) (N₀ : Type vN) (P₀ : Type vP)
    [AddCommGroup M₀] [AddCommGroup N₀] [AddCommGroup P₀]
    [Module S₀ᵐᵒᵖ M₀] [Module S₀ N₀] [Module R₀ᵐᵒᵖ N₀] [Module R₀ P₀]
    [SMulCommClass S₀ R₀ᵐᵒᵖ N₀] :
    assocSource ℤ S₀ R₀ M₀ N₀ P₀ ≃ₗ[ℤ] assocTarget ℤ S₀ R₀ M₀ N₀ P₀ :=
  assoc ℤ S₀ R₀ M₀ N₀ P₀

/-- The real old unit insertions agree through the computed associator over any ring. -/
example (D : Type vR) [Ring D]
    (U : Type vM) (V : Type vP) [AddCommGroup U] [AddCommGroup V]
    [Module Dᵐᵒᵖ U] [Module D V] (u : U) (v : V) :
    letI : SMulCommClass D Dᵐᵒᵖ D :=
      ⟨fun a b x => show a * (x * b.unop) = (a * x) * b.unop from
        (mul_assoc a x b.unop).symm⟩
    letI := rightModule ℤ D D U D
    letI := leftModule ℤ D D D V
    assoc ℤ D D U D V
        (mk ℤ D (Balanced ℤ D U D) V ((rightUnitor ℤ D U).symm u) v) =
      mk ℤ D U (Balanced ℤ D D V) u ((leftUnitor ℤ D V).symm v) := by
  let : SMulCommClass D Dᵐᵒᵖ D :=
    ⟨fun a b x => show a * (x * b.unop) = (a * x) * b.unop from
      (mul_assoc a x b.unop).symm⟩
  let := rightModule ℤ D D U D
  let := leftModule ℤ D D D V
  rw [rightUnitor_symm, leftUnitor_symm, assoc_mk_mk]

end TensorProduct.Balanced.AssociatorPublicApi
