/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Embedding
public import CSLibExt.Languages.LambdaCalculus.FOmega.Closing
public import CSLibExt.Languages.LambdaCalculus.FOmega.RelationalTypes
public import CSLibExt.Languages.LambdaCalculus.SystemF.Interpretation

/-! # System F embedding agreement with the single term/relation model -/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

open Cslib.LambdaCalculus.LocallyNameless.Untyped (Term)

private theorem eraseWith_fromSystemF {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (σ : Fin m → Term Nat) (t : SystemF.Tm n m) :
    SystemF.Tm.eraseWith σ (Tm.eraseSyntax (Tm.fromSystemF φ t)) =
      SystemF.Tm.eraseWith σ t := by
  induction t generalizing Δ with
  | var => rfl
  | lam A b ih => simp [Tm.fromSystemF, Tm.eraseSyntax, ih]
  | app f a ihf iha => simp [Tm.fromSystemF, Tm.eraseSyntax, ihf, iha]
  | tabs b ih => simp [Tm.fromSystemF, Tm.eraseSyntax, ih]
  | tapp f A ih => simp [Tm.fromSystemF, Tm.eraseSyntax, ih]

/-- Translated System F terms have exactly the same model closing instances. -/
theorem Tm.close_fromSystemF {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (σ : Fin m → SystemF.Model) (t : SystemF.Tm n m) :
    close σ (fromSystemF φ t) = SystemF.Tm.close σ t := by
  apply Subtype.ext
  exact eraseWith_fromSystemF φ (fun i => (σ i).val) t

/-- Canonical embedding preserves arbitrary model closing instances exactly. -/
theorem Tm.close_embed {n m : Nat} (σ : Fin m → SystemF.Model)
    (t : SystemF.Tm n m) : close σ (Tm.embed t) = SystemF.Tm.close σ t :=
  close_fromSystemF (fun i => .var (KVar.ofFin i)) σ t

/-- A System F term and its Fω embedding have identical model erasures. -/
theorem Tm.eraseModel_embed {n : Nat} (t : SystemF.Tm n 0) :
    eraseModel (Tm.embed t) = SystemF.Tm.eraseModel t := close_embed Fin.elim0 t

private theorem interpret_liftTypes {n : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (ρ : KEnv SystemF.Rel Δ) (R : SystemF.Rel)
    (i : Fin (n + 1)) :
    (liftTypes φ i).interpret (KEnv.extend (κ := .star) ρ R) =
      Fin.cases R (fun j => (φ j).interpret ρ) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => exact Ty.interpret_weaken (μ := .star) (φ i) ρ R

/-- The star/forall translation preserves the same binary type interpretation. -/
theorem Ty.interpret_fromSystemF {n : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (ρ : KEnv SystemF.Rel Δ) (A : SystemF.Ty n) :
    (fromSystemF φ A).interpret ρ =
      A.interpret (fun i => (φ i).interpret ρ) := by
  induction A generalizing Δ with
  | var => rfl
  | arr A B ihA ihB =>
    change SystemF.Rel.arrow ((fromSystemF φ A).interpret ρ)
      ((fromSystemF φ B).interpret ρ) =
      SystemF.Rel.arrow (A.interpret (fun i => (φ i).interpret ρ))
        (B.interpret (fun i => (φ i).interpret ρ))
    rw [ihA, ihB]
  | all B ih =>
    change SystemF.Rel.universal (fun R : SystemF.Rel =>
      (fromSystemF (liftTypes φ) B).interpret (KEnv.extend (κ := .star) ρ R)) =
      SystemF.Rel.universal (fun R : SystemF.Rel =>
        B.interpret (Fin.cases R (fun i => (φ i).interpret ρ)))
    congr 1
    funext R
    rw [ih]
    congr 1
    funext i
    exact interpret_liftTypes φ ρ R i

/-- Canonical embedding interprets each source variable by its matching kinded lookup. -/
theorem Ty.interpret_embed {n : Nat} (A : SystemF.Ty n)
    (ρ : KEnv SystemF.Rel (List.replicate n .star)) :
    (Ty.embed A).interpret ρ = A.interpret (fun i => ρ (KVar.ofFin i)) :=
  interpret_fromSystemF (fun i => .var (KVar.ofFin i)) ρ A

end Cslib.Languages.LambdaCalculus.FOmega
