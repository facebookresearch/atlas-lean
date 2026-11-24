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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions

/-!
# The concrete noncommutative balanced tensor associator

The maps use the existing quotient and its universal lift twice. The middle
factor has its given commuting left/right actions. Computed outer actions
provide the two nested balancing dictionaries; the original ground modules
are retained. No monoidal structure or associator is supplied as data.
-/

@[expose] public section

noncomputable section

open MulOpposite

universe u vS vR vM vN vP vM' vN' vP' vQ vT

namespace TensorProduct.Balanced

variable (k : Type u) (S : Type vS) (R : Type vR)
  (M : Type vM) (N : Type vN) (P : Type vP)
  [CommRing k] [Semiring S] [Semiring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module Sᵐᵒᵖ M] [Module S N] [Module Rᵐᵒᵖ N] [Module R P]
  [SMulCommClass S k N] [SMulCommClass Rᵐᵒᵖ k N]
  [SMulCommClass S Rᵐᵒᵖ N]

/-- The literal left-parenthesized quotient with its earned inner right action. -/
abbrev assocSource :=
  @Balanced k R (Balanced k S M N) P
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (rightModule k S R M N) inferInstance

/-- The literal right-parenthesized quotient, retaining its original ground module. -/
abbrev assocTarget :=
  @Balanced k S M (Balanced k R N P)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (leftModule k R S N P)

/-- Move parentheses to the right by the actual balanced universal maps. -/
def assocHom : assocSource k S R M N P →ₗ[k] assocTarget k S R M N P := by
  letI := rightModule k S R M N
  letI := leftModule k R S N P
  let X := Balanced k S M N
  let Y := Balanced k R N P
  let T := assocTarget k S R M N P
  let G : P →ₗ[k] X →ₗ[k] T :=
    { toFun := fun p =>
        lift ((mk k S M Y).compl₂ ((mk k R N P).flip p)) (by
          intro s m n
          change mk k S M Y (op s • m) (mk k R N P n p) =
            mk k S M Y m (mk k R N P (s • n) p)
          rw [balance, leftModule_smul_mk])
      map_add' := by
        intro p p'
        apply hom_ext
        intro m n
        change mk k S M Y m (mk k R N P n (p + p')) =
          mk k S M Y m (mk k R N P n p) + mk k S M Y m (mk k R N P n p')
        rw [map_add, map_add]
      map_smul' := by
        intro c p
        apply hom_ext
        intro m n
        change mk k S M Y m (mk k R N P n (c • p)) =
          c • mk k S M Y m (mk k R N P n p)
        rw [map_smul, map_smul] }
  refine lift G.flip ?_
  intro r x p
  have e : (G p).comp (rightAction k S R M N (op r)) = G (r • p) := by
    apply hom_ext
    intro m n
    change G p (rightAction k S R M N (op r) (mk k S M N m n)) =
      G (r • p) (mk k S M N m n)
    rw [rightAction_mk]
    change mk k S M Y m (mk k R N P (op r • n) p) =
      mk k S M Y m (mk k R N P n (r • p))
    exact congrArg (mk k S M Y m) (balance k R N P r n p)
  change G p (rightAction k S R M N (op r) x) = G (r • p) x
  exact congrArg (fun l : X →ₗ[k] T => l x) e

/-- The forward map preserves the original ordered triple of pure factors. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem assocHom_mk_mk (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    assocHom k S R M N P
        (mk k R (Balanced k S M N) P (mk k S M N m n) p) =
      mk k S M (Balanced k R N P) m (mk k R N P n p) := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  rfl

/-- Move parentheses to the left through the same original balancing relations. -/
def assocInv : assocTarget k S R M N P →ₗ[k] assocSource k S R M N P := by
  letI := rightModule k S R M N
  letI := leftModule k R S N P
  let X := Balanced k S M N
  let Y := Balanced k R N P
  let T := assocSource k S R M N P
  let G : M →ₗ[k] Y →ₗ[k] T :=
    { toFun := fun m =>
        lift ((mk k R X P).comp (mk k S M N m)) (by
          intro r n p
          change mk k R X P (mk k S M N m (op r • n)) p =
            mk k R X P (mk k S M N m n) (r • p)
          calc
            _ = mk k R X P (op r • mk k S M N m n) p :=
              congrArg (fun x : X => mk k R X P x p)
                (rightModule_smul_mk k S R M N (op r) m n).symm
            _ = _ := balance k R X P r (mk k S M N m n) p)
      map_add' := by
        intro m m'
        apply hom_ext
        intro n p
        change mk k R X P (mk k S M N (m + m') n) p =
          mk k R X P (mk k S M N m n) p + mk k R X P (mk k S M N m' n) p
        simp only [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c m
        apply hom_ext
        intro n p
        change mk k R X P (mk k S M N (c • m) n) p =
          c • mk k R X P (mk k S M N m n) p
        simp only [map_smul, LinearMap.smul_apply] }
  refine lift G ?_
  intro s m y
  have e : G (op s • m) = (G m).comp (leftAction k R S N P s) := by
    apply hom_ext
    intro n p
    change G (op s • m) (mk k R N P n p) =
      G m (leftAction k R S N P s (mk k R N P n p))
    rw [leftAction_mk]
    change mk k R X P (mk k S M N (op s • m) n) p =
      mk k R X P (mk k S M N m (s • n)) p
    exact congrArg (fun x : X => mk k R X P x p) (balance k S M N s m n)
  change G (op s • m) y = G m (leftAction k R S N P s y)
  exact congrArg (fun l : Y →ₗ[k] T => l y) e

/-- The inverse returns the same ordered pure factors to the left parentheses. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem assocInv_mk_mk (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    assocInv k S R M N P
        (mk k S M (Balanced k R N P) m (mk k R N P n p)) =
      mk k R (Balanced k S M N) P (mk k S M N m n) p := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  rfl

/-- The actual inverse followed by the forward map is the identity. -/
theorem assocHom_comp_assocInv :
    (assocHom k S R M N P).comp (assocInv k S R M N P) = LinearMap.id := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let Y := Balanced k R N P
  apply hom_ext
  intro m y
  have e : ((assocHom k S R M N P).comp (assocInv k S R M N P)).comp
      (mk k S M Y m) = mk k S M Y m := by
    apply hom_ext
    intro n p
    change assocHom k S R M N P
      (assocInv k S R M N P (mk k S M Y m (mk k R N P n p))) =
        mk k S M Y m (mk k R N P n p)
    exact (congrArg (assocHom k S R M N P)
      (assocInv_mk_mk k S R M N P m n p)).trans
        (assocHom_mk_mk k S R M N P m n p)
  change assocHom k S R M N P (assocInv k S R M N P (mk k S M Y m y)) =
    mk k S M Y m y
  exact congrArg (fun l => l y) e

/-- The forward map followed by the actual inverse is the identity. -/
theorem assocInv_comp_assocHom :
    (assocInv k S R M N P).comp (assocHom k S R M N P) = LinearMap.id := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let X := Balanced k S M N
  apply hom_ext
  intro x p
  have e : ((assocInv k S R M N P).comp (assocHom k S R M N P)).comp
      ((mk k R X P).flip p) = (mk k R X P).flip p := by
    apply hom_ext
    intro m n
    change assocInv k S R M N P
      (assocHom k S R M N P (mk k R X P (mk k S M N m n) p)) =
        mk k R X P (mk k S M N m n) p
    exact (congrArg (assocInv k S R M N P)
      (assocHom_mk_mk k S R M N P m n p)).trans
        (assocInv_mk_mk k S R M N P m n p)
  change assocInv k S R M N P (assocHom k S R M N P (mk k R X P x p)) =
    mk k R X P x p
  exact congrArg (fun l => l x) e

/-- The earned associator of the literal noncommutative balanced quotients. -/
def assoc : assocSource k S R M N P ≃ₗ[k] assocTarget k S R M N P :=
  LinearEquiv.ofLinearMap (assocHom k S R M N P) (assocInv k S R M N P)
    (assocHom_comp_assocInv k S R M N P) (assocInv_comp_assocHom k S R M N P)

@[simp]
theorem assoc_toLinearMap : (assoc k S R M N P).toLinearMap =
    assocHom k S R M N P := rfl

@[simp]
theorem assoc_symm_toLinearMap : (assoc k S R M N P).symm.toLinearMap =
    assocInv k S R M N P := rfl

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem assoc_mk_mk (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    assoc k S R M N P
        (mk k R (Balanced k S M N) P (mk k S M N m n) p) =
      mk k S M (Balanced k R N P) m (mk k R N P n p) := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  exact assocHom_mk_mk k S R M N P m n p

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem assoc_symm_mk_mk (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    (assoc k S R M N P).symm
        (mk k S M (Balanced k R N P) m (mk k R N P n p)) =
      mk k R (Balanced k S M N) P (mk k S M N m n) p := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  exact assocInv_mk_mk k S R M N P m n p

section Naturality

variable {k S R M N P}
  {M' : Type vM'} {N' : Type vN'} {P' : Type vP'}
  [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
  [Module k M'] [Module k N'] [Module k P']
  [Module Sᵐᵒᵖ M'] [Module S N'] [Module Rᵐᵒᵖ N'] [Module R P']
  [SMulCommClass S k N'] [SMulCommClass Rᵐᵒᵖ k N']
  [SMulCommClass S Rᵐᵒᵖ N']
  (f : M →ₗ[k] M') (g : N →ₗ[k] N') (h : P →ₗ[k] P')
  (fS : ∀ (s : S) (m : M), f (op s • m) = op s • f m)
  (gS : ∀ (s : S) (n : N), g (s • n) = s • g n)
  (gR : ∀ (t : Rᵐᵒᵖ) (n : N), g (t • n) = t • g n)
  (hR : ∀ (r : R) (p : P), h (r • p) = r • h p)

/-- The actual triple coefficient map on the left parentheses, with earned inner equivariance. -/
def mapAssocSource : assocSource k S R M N P →ₗ[k] assocSource k S R M' N' P' := by
  letI := rightModule k S R M N
  letI := rightModule k S R M' N'
  let X := Balanced k S M N
  let X' := Balanced k S M' N'
  let l : X →ₗ[k] X' := map f g fS gS
  have hl : ∀ (r : R) (x : X), l (op r • x) = op r • l x := by
    intro r x
    change l (rightAction k S R M N (op r) x) =
      rightAction k S R M' N' (op r) (l x)
    exact congrArg (fun a : X →ₗ[k] X' => a x)
      (map_rightAction f g fS gS gR (op r))
  exact map l h hl hR

/-- The same original coefficient maps on the right parentheses. -/
def mapAssocTarget : assocTarget k S R M N P →ₗ[k] assocTarget k S R M' N' P' := by
  letI := leftModule k R S N P
  letI := leftModule k R S N' P'
  let Y := Balanced k R N P
  let Y' := Balanced k R N' P'
  let l : Y →ₗ[k] Y' := map g h (fun r n => gR (op r) n) hR
  have hl : ∀ (s : S) (y : Y), l (s • y) = s • l y := by
    intro s y
    change l (leftAction k R S N P s y) = leftAction k R S N' P' s (l y)
    exact congrArg (fun a : Y →ₗ[k] Y' => a y)
      (map_leftAction g h (fun r n => gR (op r) n) hR gS s)
  exact map f l fS hl

omit [SMulCommClass S k N] [SMulCommClass S k N'] in
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem mapAssocSource_mk_mk (m : M) (n : N) (p : P) :
    letI := rightModule k S R M N
    letI := rightModule k S R M' N'
    mapAssocSource f g h fS gS gR hR
        (mk k R (Balanced k S M N) P (mk k S M N m n) p) =
      mk k R (Balanced k S M' N') P' (mk k S M' N' (f m) (g n)) (h p) := by
  let := rightModule k S R M N
  let := rightModule k S R M' N'
  simp only [mapAssocSource, map_mk]

omit [SMulCommClass Rᵐᵒᵖ k N] [SMulCommClass Rᵐᵒᵖ k N'] in
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem mapAssocTarget_mk_mk (m : M) (n : N) (p : P) :
    letI := leftModule k R S N P
    letI := leftModule k R S N' P'
    mapAssocTarget f g h fS gS gR hR
        (mk k S M (Balanced k R N P) m (mk k R N P n p)) =
      mk k S M' (Balanced k R N' P') (f m) (mk k R N' P' (g n) (h p)) := by
  let := leftModule k R S N P
  let := leftModule k R S N' P'
  simp only [mapAssocTarget, map_mk]

/-- Reassociation is natural in all three actual equivariant coefficient maps. -/
theorem assocHom_naturality :
    (assocHom k S R M' N' P').comp (mapAssocSource f g h fS gS gR hR) =
      (mapAssocTarget f g h fS gS gR hR).comp (assocHom k S R M N P) := by
  let := rightModule k S R M N
  let := rightModule k S R M' N'
  let := leftModule k R S N P
  let := leftModule k R S N' P'
  let X := Balanced k S M N
  apply hom_ext
  intro x p
  have e : ((assocHom k S R M' N' P').comp (mapAssocSource f g h fS gS gR hR)).comp
      ((mk k R X P).flip p) =
      ((mapAssocTarget f g h fS gS gR hR).comp (assocHom k S R M N P)).comp
        ((mk k R X P).flip p) := by
    apply hom_ext
    intro m n
    change assocHom k S R M' N' P'
      (mapAssocSource f g h fS gS gR hR (mk k R X P (mk k S M N m n) p)) =
        mapAssocTarget f g h fS gS gR hR
          (assocHom k S R M N P (mk k R X P (mk k S M N m n) p))
    calc
      _ = assocHom k S R M' N' P'
          (mk k R (Balanced k S M' N') P' (mk k S M' N' (f m) (g n)) (h p)) :=
        congrArg (assocHom k S R M' N' P')
          (mapAssocSource_mk_mk (k := k) (S := S) (R := R)
            (M := M) (N := N) (P := P) (M' := M') (N' := N') (P' := P')
            f g h fS gS gR hR m n p)
      _ = mk k S M' (Balanced k R N' P') (f m)
          (mk k R N' P' (g n) (h p)) :=
        assocHom_mk_mk k S R M' N' P' (f m) (g n) (h p)
      _ = mapAssocTarget f g h fS gS gR hR
          (mk k S M (Balanced k R N P) m (mk k R N P n p)) :=
        (mapAssocTarget_mk_mk (k := k) (S := S) (R := R)
          (M := M) (N := N) (P := P) (M' := M') (N' := N') (P' := P')
          f g h fS gS gR hR m n p).symm
      _ = _ := (congrArg (mapAssocTarget f g h fS gS gR hR)
        (assocHom_mk_mk k S R M N P m n p)).symm
  change assocHom k S R M' N' P' (mapAssocSource f g h fS gS gR hR (mk k R X P x p)) =
    mapAssocTarget f g h fS gS gR hR (assocHom k S R M N P (mk k R X P x p))
  exact congrArg (fun l => l x) e

end Naturality

section CommutingOuterActions

variable (Q : Type vQ) [Semiring Q] [Module Q M]
  [SMulCommClass Q k M] [SMulCommClass Q Sᵐᵒᵖ M]

set_option linter.unusedSectionVars false in
/-- The earned actions on opposite factors of a balanced quotient commute. -/
@[nolint unusedArguments] -- omitting it would shrink `leftRightSMulCommClass` for all users
theorem left_rightAction_comm (q : Q) (t : Rᵐᵒᵖ) :
    (leftAction k S Q M N q).comp (rightAction k S R M N t) =
      (rightAction k S R M N t).comp (leftAction k S Q M N q) := by
  apply hom_ext
  intro m n
  simp only [LinearMap.comp_apply, leftAction_mk, rightAction_mk]

/-- Both computed outer modules form a genuine commuting-action dictionary. -/
theorem leftRightSMulCommClass :
    letI := leftModule k S Q M N
    letI := rightModule k S R M N
    SMulCommClass Q Rᵐᵒᵖ (Balanced k S M N) := by
  let := leftModule k S Q M N
  let := rightModule k S R M N
  refine ⟨fun q t x => ?_⟩
  change leftAction k S Q M N q (rightAction k S R M N t x) =
    rightAction k S R M N t (leftAction k S Q M N q x)
  exact congrArg (fun l : Balanced k S M N →ₗ[k] Balanced k S M N => l x)
    (left_rightAction_comm k S R M N Q q t)

end CommutingOuterActions

section OuterLeft

variable (Q : Type vQ) [Semiring Q] [Module Q M]
  [SMulCommClass Q k M] [SMulCommClass Q Sᵐᵒᵖ M]

private theorem assocHom_leftAction (q : Q) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := leftModule k S Q M N
    letI := leftSMulCommClass k S Q M N
    letI := leftRightSMulCommClass k S R M N Q
    (assocHom k S R M N P).comp (leftAction k R Q (Balanced k S M N) P q) =
      (leftAction k S Q M (Balanced k R N P) q).comp (assocHom k S R M N P) := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let := leftModule k S Q M N
  let := leftSMulCommClass k S Q M N
  let := leftRightSMulCommClass k S R M N Q
  let X := Balanced k S M N
  let Y := Balanced k R N P
  apply hom_ext
  intro x p
  have e : ((assocHom k S R M N P).comp ((mk k R X P).flip p)).comp
      (leftAction k S Q M N q) =
      ((leftAction k S Q M Y q).comp (assocHom k S R M N P)).comp
        ((mk k R X P).flip p) := by
    apply hom_ext
    intro m n
    change assocHom k S R M N P
        (mk k R X P (leftAction k S Q M N q (mk k S M N m n)) p) =
      leftAction k S Q M Y q
        (assocHom k S R M N P (mk k R X P (mk k S M N m n) p))
    calc
      _ = assocHom k S R M N P (mk k R X P (mk k S M N (q • m) n) p) :=
        congrArg (fun z : Balanced k S M N =>
          assocHom k S R M N P (mk k R X P z p))
          (leftAction_mk k S Q M N q m n)
      _ = mk k S M Y (q • m) (mk k R N P n p) :=
        assocHom_mk_mk k S R M N P (q • m) n p
      _ = leftAction k S Q M Y q (mk k S M Y m (mk k R N P n p)) :=
        (leftAction_mk k S Q M Y q m (mk k R N P n p)).symm
      _ = _ := (congrArg (leftAction k S Q M Y q)
        (assocHom_mk_mk k S R M N P m n p)).symm
  simp only [LinearMap.comp_apply, leftAction_mk]
  change assocHom k S R M N P (mk k R X P (leftAction k S Q M N q x) p) =
    leftAction k S Q M Y q (assocHom k S R M N P (mk k R X P x p))
  exact congrArg (fun l => l x) e

/-- Reassociation is linear for the actual twice-computed left outer action. -/
theorem assoc_left_smul (q : Q) (x : assocSource k S R M N P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := leftModule k S Q M N
    letI := leftSMulCommClass k S Q M N
    letI := leftRightSMulCommClass k S R M N Q
    letI := leftModule k R Q (Balanced k S M N) P
    letI := leftModule k S Q M (Balanced k R N P)
    assoc k S R M N P (q • x) = q • assoc k S R M N P x := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let := leftModule k S Q M N
  let := leftSMulCommClass k S Q M N
  let := leftRightSMulCommClass k S R M N Q
  let := leftModule k R Q (Balanced k S M N) P
  let := leftModule k S Q M (Balanced k R N P)
  change assocHom k S R M N P (leftAction k R Q (Balanced k S M N) P q x) =
    leftAction k S Q M (Balanced k R N P) q (assocHom k S R M N P x)
  exact congrArg (fun l => l x) (assocHom_leftAction k S R M N P Q q)

end OuterLeft

section OuterRight

variable (T : Type vT) [Semiring T] [Module Tᵐᵒᵖ P]
  [SMulCommClass Tᵐᵒᵖ k P] [SMulCommClass R Tᵐᵒᵖ P]

private theorem assocHom_rightAction (t : Tᵐᵒᵖ) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := rightModule k R T N P
    letI := rightSMulCommClass k R T N P
    letI := leftRightSMulCommClass_of_factor_actions k R S T N P
    (assocHom k S R M N P).comp (rightAction k R T (Balanced k S M N) P t) =
      (rightAction k S T M (Balanced k R N P) t).comp (assocHom k S R M N P) := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let := rightModule k R T N P
  let := rightSMulCommClass k R T N P
  let := leftRightSMulCommClass_of_factor_actions k R S T N P
  let X := Balanced k S M N
  let Y := Balanced k R N P
  apply hom_ext
  intro x p
  have e : (assocHom k S R M N P).comp ((mk k R X P).flip (t • p)) =
      ((rightAction k S T M Y t).comp (assocHom k S R M N P)).comp
        ((mk k R X P).flip p) := by
    apply hom_ext
    intro m n
    change assocHom k S R M N P (mk k R X P (mk k S M N m n) (t • p)) =
      rightAction k S T M Y t
        (assocHom k S R M N P (mk k R X P (mk k S M N m n) p))
    calc
      _ = mk k S M Y m (mk k R N P n (t • p)) :=
        assocHom_mk_mk k S R M N P m n (t • p)
      _ = mk k S M Y m (t • mk k R N P n p) :=
        congrArg (mk k S M Y m) (rightModule_smul_mk k R T N P t n p).symm
      _ = rightAction k S T M Y t (mk k S M Y m (mk k R N P n p)) :=
        (rightAction_mk k S T M Y t m (mk k R N P n p)).symm
      _ = _ := (congrArg (rightAction k S T M Y t)
        (assocHom_mk_mk k S R M N P m n p)).symm
  simp only [LinearMap.comp_apply, rightAction_mk]
  change assocHom k S R M N P (mk k R X P x (t • p)) =
    rightAction k S T M Y t (assocHom k S R M N P (mk k R X P x p))
  exact congrArg (fun l => l x) e

/-- The original right outer action is also preserved by the earned associator. -/
theorem assoc_right_smul (t : Tᵐᵒᵖ) (x : assocSource k S R M N P) :
    letI := rightModule k S R M N
    letI := leftModule k R S N P
    letI := rightModule k R T N P
    letI := rightSMulCommClass k R T N P
    letI := leftRightSMulCommClass_of_factor_actions k R S T N P
    letI := rightModule k R T (Balanced k S M N) P
    letI := rightModule k S T M (Balanced k R N P)
    assoc k S R M N P (t • x) = t • assoc k S R M N P x := by
  let := rightModule k S R M N
  let := leftModule k R S N P
  let := rightModule k R T N P
  let := rightSMulCommClass k R T N P
  let := leftRightSMulCommClass_of_factor_actions k R S T N P
  let := rightModule k R T (Balanced k S M N) P
  let := rightModule k S T M (Balanced k R N P)
  change assocHom k S R M N P (rightAction k R T (Balanced k S M N) P t x) =
    rightAction k S T M (Balanced k R N P) t (assocHom k S R M N P x)
  exact congrArg (fun l => l x) (assocHom_rightAction k S R M N P T t)

end OuterRight

end TensorProduct.Balanced
