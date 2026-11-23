/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore

/-!
# Point transport for native covers
-/

/-! The original native map and both pulled-cover projections commute with
literal point equality transports. These are computed equality maps, with
no point-matching or cover-model witness. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

public section

namespace SSet.KanComplex

theorem nativeCoverPointTransport_projection {B : SSet.{u}} {b c : B _⦋0⦌} (h : b = c) :
    eqToHom (congrArg (nativeCover B) h) ≫ nativeCoverProjection B c =
      nativeCoverProjection B b := by
  cases h
  exact (Category.id_comp _)

theorem nativeCoverPulledPointTransport_fst {E B : SSet.{u}} (p : E ⟶ B)
    {b c : B _⦋0⦌} (h : b = c) :
    eqToHom (congrArg (fun z => pullback p (nativeCoverProjection B z)) h) ≫
        pullback.fst p (nativeCoverProjection B c) =
      pullback.fst p (nativeCoverProjection B b) := by
  cases h
  exact (Category.id_comp _)

theorem nativeCoverPulledPointTransport_snd {E B : SSet.{u}} (p : E ⟶ B)
    {b c : B _⦋0⦌} (h : b = c) :
    eqToHom (congrArg (fun z => pullback p (nativeCoverProjection B z)) h) ≫
        pullback.snd p (nativeCoverProjection B c) =
      pullback.snd p (nativeCoverProjection B b) ≫ eqToHom (congrArg (nativeCover B) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Equality of the original maps gives the SAME induced native map with its literal target cast. -/
theorem nativeCoverMap_congr {A B : SSet.{u}} {f g : A ⟶ B} (h : f = g) (a : A _⦋0⦌) :
    nativeCoverMap f a ≫ eqToHom (congrArg (nativeCover B)
      (congrArg (fun k : A ⟶ B => k.app (op ⦋0⦌) a) h)) = nativeCoverMap g a := by
  cases h
  exact Category.comp_id _

/-- The complete original commuting square is retained through the computed target point cast. -/
theorem nativeCoverMap_commutingSquare {A B C D : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (a : A _⦋0⦌) :
    (nativeCoverMap f a ≫ nativeCoverMap g (f.app (op ⦋0⦌) a)) ≫
        eqToHom (congrArg (nativeCover D)
          (congrArg (fun l : A ⟶ D => l.app (op ⦋0⦌) a) w)) =
      nativeCoverMap h a ≫ nativeCoverMap k (h.app (op ⦋0⦌) a) :=
  (congrArg (fun l => l ≫ eqToHom (congrArg (nativeCover D)
      (congrArg (fun m : A ⟶ D => m.app (op ⦋0⦌) a) w))) (nativeCoverMap_comp f g a)).trans
    ((nativeCoverMap_congr w a).trans (nativeCoverMap_comp h k a).symm)

end SSet.KanComplex
