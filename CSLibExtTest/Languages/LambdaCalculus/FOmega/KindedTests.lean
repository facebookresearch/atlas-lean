/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.FOmega.Confluence

/-! # Kind, capture and beta-conversion probes for pure Fω -/

open Cslib.Languages.LambdaCalculus.FOmega

private def opId {Δ : List Kind} {κ : Kind} : Ty Δ (.arrow κ κ) :=
  .lam (.var .zero)

private def poly {Δ : List Kind} : Ty Δ .star :=
  .all (κ := .star) (.arr (.var .zero) (.var .zero))

example : Ty.instantiate (.var .zero) (poly : Ty [] .star) = poly := rfl

example : Ty.Conv (.app opId (poly : Ty [] .star)) poly :=
  .beta _ _

example : Ty.Conv
    (.all (κ := .star) (.app opId (.var .zero)) : Ty [] .star)
    (.all (.var .zero)) := .all (.beta _ _)

example : Ty.Conv
    (.lam (.app opId (.var .zero)) : Ty [] (.arrow .star .star))
    (.lam (.var .zero)) := .lam (.beta _ _)

private def quantifiedCapture {Δ : List Kind} : Ty (.star :: Δ) .star :=
  .all (κ := .star) (.arr (.var (.succ .zero)) (.var .zero))

example (a : Ty [.star] .star) :
    Ty.instantiate quantifiedCapture a =
      .all (.arr (Ty.rename KVar.succ a) (.var .zero)) := rfl

example : Ty.instantiate quantifiedCapture (.var .zero : Ty [.star] .star) =
    .all (.arr (.var (.succ .zero)) (.var .zero)) := rfl

private def operatorCapture {Δ : List Kind} :
    Ty (.arrow .star .star :: Δ) (.arrow .star .star) :=
  .lam (.app (.var (.succ .zero)) (.var .zero))

example (f : Ty [.arrow .star .star] (.arrow .star .star)) :
    Ty.instantiate operatorCapture f =
      .lam (.app (Ty.rename KVar.succ f) (.var .zero)) := rfl

example : Ty.Conv
    (.app (Ty.instantiate operatorCapture opId) (poly : Ty [] .star)) poly :=
  .trans (.beta _ _) (.beta _ _)

example : Ty.Conv
    (.app (Ty.instantiate operatorCapture opId)
      (.arr poly poly : Ty [] .star)) (.arr poly poly) :=
  .trans (.beta _ _) (.beta _ _)

example : ¬ Ty.Conv (.arr poly poly : Ty [] .star) poly :=
  Ty.not_conv_arr_all

private def natAlgebra : KindAlgebra Nat :=
  ⟨Nat.add, fun {_} _ => 0⟩

private def natEnv (n : Nat) : KEnv Nat [.star]
  | _, .zero => n
  | _, .succ x => nomatch x

example (n : Nat) :
    Ty.eval natAlgebra (natEnv n)
      (.app (.lam (.arr (.var .zero) (.var .zero))) (.var .zero)) =
        n + n := rfl

example {Δ : List Kind} {κ μ : Kind} (M : KindAlgebra Nat)
    (ρ : KEnv Nat Δ) (b : Ty (μ :: Δ) κ) (a : Ty Δ μ) :
    Ty.eval M ρ (.app (.lam b) a) = Ty.eval M ρ (b.instantiate a) :=
  (Ty.Conv.beta b a).sound M ρ

example : Ty.Par (.app opId (poly : Ty [] .star)) poly :=
  .beta (.refl _) (.refl _)

example {Δ : List Kind} {κ : Kind} {a b c : Ty Δ κ}
    (hb : Ty.Par a b) (hc : Ty.Par a c) :
    Ty.Par b (Ty.develop a) ∧ Ty.Par c (Ty.develop a) :=
  ⟨hb.to_develop, hc.to_develop⟩

example {Δ : List Kind} {a b c d : Ty Δ .star}
    (h : Ty.Conv (.arr a b) (.arr c d)) :
    Ty.Conv a c ∧ Ty.Conv b d := h.arr_inj

example : ¬ Ty.Conv
    (.all (κ := .star) (.var .zero) : Ty [] .star)
    (.all (κ := .arrow .star .star) (.app (.var .zero) poly)) := by
  intro h
  exact Kind.noConfusion h.all_kind
