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

public import MathlibExt.LinearAlgebra.TensorProduct.ModuleMap
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator

/-!
# Morita coefficient tensors and maps

For compatible S–R, R–R and R–S bimodules Q, M and P, the coefficient is
`(Q ⊗_R M) ⊗_R P`. The S-actions on Q and P give a module over
`S ⊗[k] Sᵐᵒᵖ`.

Coefficient maps act on M, commute with scalar actions and reassociation,
and satisfy identity and composition laws.
Scalar and coefficient universes are independent; invertibility,
flatness, field and finite-dimensionality assumptions are not required.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u r s q m p n o c

namespace TensorProduct.Balanced.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R]
  (S : Type s) [Ring S] [Algebra k S]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]
  (M : Type m) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]

/-- The original left parentheses and original ground-module dictionaries. -/
abbrev coefficientTensor := assocSource k R R Q M P

set_option linter.unusedSectionVars false in
/-- Original pure triples determine an additive coefficient map. -/
@[nolint unusedArguments] -- omitting them would shrink the defs built with it, across modules
theorem coefficientHom_ext {C : Type c} [AddCommMonoid C]
    {f g : coefficientTensor k R Q M P →+ C}
    (h : letI := rightModule k R R Q M
      ∀ (q : Q) (m : M) (p : P),
        f (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) =
          g (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p)) :
    f = g := by
  let := rightModule k R R Q M
  let I := TensorProduct.Balanced k R Q M
  apply addHom_ext k R I P
  intro y p
  have hp : f.comp (((mk k R I P).flip p).toAddMonoidHom) =
      g.comp (((mk k R I P).flip p).toAddMonoidHom) := by
    apply addHom_ext k R Q M
    intro q m
    exact h q m p
  exact DFunLike.congr_fun hp y

/-- The twice-computed left S-action, on the first coefficient factor Q. -/
def coefficientLeftModule : Module S (coefficientTensor k R Q M P) := by
  letI := rightModule k R R Q M
  letI := leftModule k R S Q M
  letI := leftSMulCommClass k R S Q M
  letI := leftRightSMulCommClass k R R Q M S
  exact leftModule k R S (TensorProduct.Balanced k R Q M) P

/-- The computed right S-action, on the final coefficient factor P. -/
def coefficientRightModule : Module Sᵐᵒᵖ (coefficientTensor k R Q M P) := by
  letI := rightModule k R R Q M
  exact rightModule k R S (TensorProduct.Balanced k R Q M) P

omit [IsScalarTower k Rᵐᵒᵖ Q] in
/-- The two earned outer actions commute; this is not supplied by callers. -/
theorem coefficientActionsComm :
    letI := coefficientLeftModule k R S Q M P
    letI := coefficientRightModule k R S Q M P
    SMulCommClass S Sᵐᵒᵖ (coefficientTensor k R Q M P) := by
  let := rightModule k R R Q M
  let := leftModule k R S Q M
  let := leftSMulCommClass k R S Q M
  let := leftRightSMulCommClass k R R Q M S
  let := coefficientLeftModule k R S Q M P
  let := coefficientRightModule k R S Q M P
  exact leftRightSMulCommClass k R S (TensorProduct.Balanced k R Q M) P S

omit [IsScalarTower k Rᵐᵒᵖ Q] [SMulCommClass R Sᵐᵒᵖ P] [IsScalarTower k R P]
  [IsScalarTower k Sᵐᵒᵖ P] [Module Sᵐᵒᵖ P] in
/-- The original Q compatibility earns the left ground tower of the quotient. -/
theorem coefficientLeftTower :
    letI := coefficientLeftModule k R S Q M P
    IsScalarTower k S (coefficientTensor k R Q M P) := by
  let := rightModule k R R Q M
  let := leftModule k R S Q M
  let := leftSMulCommClass k R S Q M
  let := leftRightSMulCommClass k R R Q M S
  let := leftScalarTower k R S Q M
  let := coefficientLeftModule k R S Q M P
  exact leftScalarTower k R S (TensorProduct.Balanced k R Q M) P

omit [SMulCommClass S Rᵐᵒᵖ Q] [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]
  [IsScalarTower k R M] [IsScalarTower k R P] [Module S Q] in
/-- The original P compatibility earns the right ground tower. -/
theorem coefficientRightTower :
    letI := coefficientRightModule k R S Q M P
    IsScalarTower k Sᵐᵒᵖ (coefficientTensor k R Q M P) := by
  let := rightModule k R R Q M
  let := coefficientRightModule k R S Q M P
  exact rightScalarTower k R S (TensorProduct.Balanced k R Q M) P

/-- The actual native enveloping-module value combines these original outer actions. -/
def coefficientModule : Module (S ⊗[k] Sᵐᵒᵖ) (coefficientTensor k R Q M P) := by
  letI := coefficientLeftModule k R S Q M P
  letI := coefficientRightModule k R S Q M P
  letI := coefficientActionsComm k R S Q M P
  letI := coefficientLeftTower k R S Q M P
  letI := coefficientRightTower k R S Q M P
  exact TensorProduct.Algebra.module

set_option linter.unusedSectionVars false in
/-- Pure triples retain the printed left outer action. -/
@[nolint unusedArguments] -- omitting them cascades via `coefficientModule_tmul_mk`
theorem coefficientLeftModule_smul_mk (s : S) (q : Q) (m : M) (p : P) :
    letI := rightModule k R R Q M
    letI := coefficientLeftModule k R S Q M P
    s • mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p =
      mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M (s • q) m) p := by
  let := rightModule k R R Q M
  let := leftModule k R S Q M
  let := leftSMulCommClass k R S Q M
  let := leftRightSMulCommClass k R R Q M S
  let := coefficientLeftModule k R S Q M P
  change leftAction k R S (TensorProduct.Balanced k R Q M) P s
    (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) = _
  rw [leftAction_mk]
  change mk k R (TensorProduct.Balanced k R Q M) P
    (leftAction k R S Q M s (mk k R Q M q m)) p = _
  rw [leftAction_mk]

set_option linter.unusedSectionVars false in
/-- The original right S-action acts only on the last factor P. -/
@[nolint unusedArguments] -- omitting them cascades via `coefficientModule_tmul_mk`
theorem coefficientRightModule_smul_mk (t : Sᵐᵒᵖ) (q : Q) (m : M) (p : P) :
    letI := rightModule k R R Q M
    letI := coefficientRightModule k R S Q M P
    t • mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p =
      mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) (t • p) := by
  let := rightModule k R R Q M
  let := coefficientRightModule k R S Q M P
  change rightAction k R S (TensorProduct.Balanced k R Q M) P t
    (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) = _
  exact rightAction_mk k R S (TensorProduct.Balanced k R Q M) P t _ p

/-- The native tensor scalar has the actual ordered two-sided coefficient value. -/
theorem coefficientModule_tmul_mk (s : S) (t : Sᵐᵒᵖ) (q : Q) (m : M) (p : P) :
    letI := rightModule k R R Q M
    letI := coefficientModule k R S Q M P
    (s ⊗ₜ[k] t) • mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p =
      mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M (s • q) m) (t • p) := by
  let := rightModule k R R Q M
  let := coefficientLeftModule k R S Q M P
  let := coefficientRightModule k R S Q M P
  let := coefficientActionsComm k R S Q M P
  let := coefficientLeftTower k R S Q M P
  let := coefficientRightTower k R S Q M P
  let := coefficientModule k R S Q M P
  change TensorProduct.Algebra.moduleAux (s ⊗ₜ[k] t)
    (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) = _
  rw [TensorProduct.Algebra.moduleAux_apply, coefficientRightModule_smul_mk,
    coefficientLeftModule_smul_mk]

section Maps

variable {k R S Q M P}
  {N : Type n} [AddCommGroup N] [Module k N]
  [Module R N] [Module Rᵐᵒᵖ N] [SMulCommClass R Rᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Rᵐᵒᵖ N]

/-- The actual coefficient map is the old balanced map, with earned native S-bimodule linearity. -/
def coefficientMap
    (f : letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) :
    letI := coefficientModule k R S Q M P
    letI := coefficientModule k R S Q N P
    coefficientTensor k R Q M P →ₗ[S ⊗[k] Sᵐᵒᵖ] coefficientTensor k R Q N P := by
  letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
  let g : M →ₗ[k] N := (TensorProduct.Algebra.toLeftLinearMap f).restrictScalars k
  have gL (r : R) (m : M) : g (r • m) = r • g m :=
    (TensorProduct.Algebra.toLeftLinearMap f).map_smul r m
  have gR (t : Rᵐᵒᵖ) (m : M) : g (t • m) = t • g m :=
    (TensorProduct.Algebra.toRightLinearMap f).map_smul t m
  let I := TensorProduct.Balanced k R Q M
  let I' := TensorProduct.Balanced k R Q N
  let h : I →ₗ[k] I' := map (LinearMap.id : Q →ₗ[k] Q) g (fun _ _ => rfl) gL
  letI := rightModule k R R Q M
  letI := rightModule k R R Q N
  letI := leftModule k R S Q M
  letI := leftModule k R S Q N
  letI := leftSMulCommClass k R S Q M
  letI := leftSMulCommClass k R S Q N
  letI := leftRightSMulCommClass k R R Q M S
  letI := leftRightSMulCommClass k R R Q N S
  have hR (r : R) (x : I) : h (op r • x) = op r • h x := by
    exact LinearMap.congr_fun
      (map_rightAction (LinearMap.id : Q →ₗ[k] Q) g
        (fun _ _ => rfl) gL gR (op r)) x
  have hS (s : S) (x : I) : h (s • x) = s • h x := by
    exact LinearMap.congr_fun
      (map_leftAction (LinearMap.id : Q →ₗ[k] Q) g
        (fun _ _ => rfl) gL (fun _ _ => rfl) s) x
  let l : coefficientTensor k R Q M P →ₗ[k] coefficientTensor k R Q N P :=
    mapAssocSource (LinearMap.id : Q →ₗ[k] Q) g (LinearMap.id : P →ₗ[k] P)
      (fun _ _ => rfl) gL gR (fun _ _ => rfl)
  letI := coefficientLeftModule k R S Q M P
  letI := coefficientLeftModule k R S Q N P
  letI := coefficientRightModule k R S Q M P
  letI := coefficientRightModule k R S Q N P
  letI := coefficientActionsComm k R S Q M P
  letI := coefficientActionsComm k R S Q N P
  letI := coefficientLeftTower k R S Q M P
  letI := coefficientLeftTower k R S Q N P
  letI := coefficientRightTower k R S Q M P
  letI := coefficientRightTower k R S Q N P
  refine TensorProduct.Algebra.ofLinearMap l ?_ ?_
  · intro s x
    change l (leftAction k R S I P s x) = leftAction k R S I' P s (l x)
    exact LinearMap.congr_fun
      (map_leftAction h (LinearMap.id : P →ₗ[k] P) hR
        (fun _ _ => rfl) hS s) x
  · intro t x
    change l (rightAction k R S I P t x) = rightAction k R S I' P t (l x)
    exact LinearMap.congr_fun
      (map_rightAction h (LinearMap.id : P →ₗ[k] P) hR
        (fun _ _ => rfl) (fun _ _ => rfl) t) x

set_option linter.unusedSectionVars false in
/-- The coefficient map keeps the old ground map and its exact native quotient values. -/
@[nolint unusedArguments] -- omitting it cascades via `coefficientMap_mk` into other modules
theorem coefficientMap_apply
    (f : letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) (x : coefficientTensor k R Q M P) :
    coefficientMap (S := S) (Q := Q) (P := P) f x =
      mapAssocSource (LinearMap.id : Q →ₗ[k] Q)
        ((TensorProduct.Algebra.toLeftLinearMap f).restrictScalars k)
        (LinearMap.id : P →ₗ[k] P) (fun _ _ => rfl)
        (fun r m => (TensorProduct.Algebra.toLeftLinearMap f).map_smul r m)
        (fun t m => (TensorProduct.Algebra.toRightLinearMap f).map_smul t m)
        (fun _ _ => rfl) x := rfl

/-- Only the original middle coefficient is changed. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem coefficientMap_mk
    (f : letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) (q : Q) (m : M) (p : P) :
    letI := rightModule k R R Q M
    letI := rightModule k R R Q N
    coefficientMap (S := S) (Q := Q) (P := P) f
        (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) =
      mk k R (TensorProduct.Balanced k R Q N) P (mk k R Q N q (f m)) p := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
  let g : M →ₗ[k] N := (TensorProduct.Algebra.toLeftLinearMap f).restrictScalars k
  have gL : ∀ (r : R) (m : M), g (r • m) = r • g m := by
    intro r m
    change (TensorProduct.Algebra.toLeftLinearMap f) (r • m) =
      r • (TensorProduct.Algebra.toLeftLinearMap f) m
    exact (TensorProduct.Algebra.toLeftLinearMap f).map_smul r m
  have gR : ∀ (t : Rᵐᵒᵖ) (m : M), g (t • m) = t • g m := by
    intro t m
    change (TensorProduct.Algebra.toRightLinearMap f) (t • m) =
      t • (TensorProduct.Algebra.toRightLinearMap f) m
    exact (TensorProduct.Algebra.toRightLinearMap f).map_smul t m
  let := rightModule k R R Q M
  let := rightModule k R R Q N
  have h : coefficientMap (S := S) (Q := Q) (P := P) f
      (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) =
    mapAssocSource (k := k) (S := R) (R := R)
      (M := Q) (N := M) (P := P) (M' := Q) (N' := N) (P' := P)
      (LinearMap.id : Q →ₗ[k] Q) g (LinearMap.id : P →ₗ[k] P)
      (fun _ _ => rfl) gL gR (fun _ _ => rfl)
      (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) :=
    coefficientMap_apply (k := k) (R := R) (S := S) (Q := Q) (M := M) (P := P)
      (N := N) f (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p)
  exact h.trans
    ((mapAssocSource_mk_mk (k := k) (S := R) (R := R)
      (M := Q) (N := M) (P := P) (M' := Q) (N' := N) (P' := P)
      (LinearMap.id : Q →ₗ[k] Q) g (LinearMap.id : P →ₗ[k] P)
      (fun _ _ => rfl) gL gR (fun _ _ => rfl) q m p).trans (by rfl))

/-- Reassociation is natural for the actual native bimodule coefficient morphism. -/
theorem coefficientMap_assoc
    (f : letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) (x : coefficientTensor k R Q M P) :
    assoc k R R Q N P (coefficientMap (S := S) (Q := Q) (P := P) f x) =
      mapAssocTarget (LinearMap.id : Q →ₗ[k] Q)
        ((TensorProduct.Algebra.toLeftLinearMap f).restrictScalars k)
        (LinearMap.id : P →ₗ[k] P) (fun _ _ => rfl)
        (fun r m => (TensorProduct.Algebra.toLeftLinearMap f).map_smul r m)
        (fun t m => (TensorProduct.Algebra.toRightLinearMap f).map_smul t m)
        (fun _ _ => rfl) (assoc k R R Q M P x) := by
  rw [coefficientMap_apply]
  exact LinearMap.congr_fun
    (assocHom_naturality (LinearMap.id : Q →ₗ[k] Q)
      ((TensorProduct.Algebra.toLeftLinearMap f).restrictScalars k)
      (LinearMap.id : P →ₗ[k] P) (fun _ _ => rfl)
      (fun r m => (TensorProduct.Algebra.toLeftLinearMap f).map_smul r m)
      (fun t m => (TensorProduct.Algebra.toRightLinearMap f).map_smul t m)
      (fun _ _ => rfl)) x

end Maps

section FunctorLaws

variable {k R S Q M P}

/-- The actual coefficient construction preserves the native identity morphism. -/
@[simp]
theorem coefficientMap_id :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    letI := coefficientModule k R S Q M P
    coefficientMap (S := S) (Q := Q) (P := P) (LinearMap.id : M →ₗ[R ⊗[k] Rᵐᵒᵖ] M) =
      LinearMap.id := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let := coefficientModule k R S Q M P
  let := rightModule k R R Q M
  apply LinearMap.toAddMonoidHom_injective
  apply coefficientHom_ext k R Q M P
  intro q m p
  change coefficientMap (S := S) (Q := Q) (P := P)
      (LinearMap.id : M →ₗ[R ⊗[k] Rᵐᵒᵖ] M)
      (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) =
    mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p
  exact (coefficientMap_mk (k := k) (R := R) (S := S) (Q := Q) (M := M)
    (P := P) (N := M) (LinearMap.id : M →ₗ[R ⊗[k] Rᵐᵒᵖ] M) q m p).trans (by rfl)

variable {N : Type n} {O : Type o}
  [AddCommGroup N] [AddCommGroup O] [Module k N] [Module k O]
  [Module R N] [Module Rᵐᵒᵖ N] [Module R O] [Module Rᵐᵒᵖ O]
  [SMulCommClass R Rᵐᵒᵖ N] [SMulCommClass R Rᵐᵒᵖ O]
  [IsScalarTower k R N] [IsScalarTower k Rᵐᵒᵖ N]
  [IsScalarTower k R O] [IsScalarTower k Rᵐᵒᵖ O]

/-- The same chosen coefficient maps preserve composition. -/
theorem coefficientMap_comp
    (f : letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      M →ₗ[R ⊗[k] Rᵐᵒᵖ] N)
    (g : letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
      letI : Module (R ⊗[k] Rᵐᵒᵖ) O := TensorProduct.Algebra.module
      N →ₗ[R ⊗[k] Rᵐᵒᵖ] O) :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    letI : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
    letI : Module (R ⊗[k] Rᵐᵒᵖ) O := TensorProduct.Algebra.module
    letI := coefficientModule k R S Q M P
    letI := coefficientModule k R S Q N P
    letI := coefficientModule k R S Q O P
    coefficientMap (S := S) (Q := Q) (P := P) (g.comp f) =
      (coefficientMap (S := S) (Q := Q) (P := P) g).comp
        (coefficientMap (S := S) (Q := Q) (P := P) f) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let : Module (R ⊗[k] Rᵐᵒᵖ) N := TensorProduct.Algebra.module
  let : Module (R ⊗[k] Rᵐᵒᵖ) O := TensorProduct.Algebra.module
  let := coefficientModule k R S Q M P
  let := coefficientModule k R S Q N P
  let := coefficientModule k R S Q O P
  let := rightModule k R R Q M
  let := rightModule k R R Q N
  let := rightModule k R R Q O
  apply LinearMap.toAddMonoidHom_injective
  apply coefficientHom_ext k R Q M P
  intro q m p
  change coefficientMap (S := S) (Q := Q) (P := P) (g.comp f)
      (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p) =
    coefficientMap (S := S) (Q := Q) (P := P) g
      (coefficientMap (S := S) (Q := Q) (P := P) f
        (mk k R (TensorProduct.Balanced k R Q M) P (mk k R Q M q m) p))
  rw [coefficientMap_mk, coefficientMap_mk, coefficientMap_mk]
  rfl

end FunctorLaws

end TensorProduct.Balanced.Morita
