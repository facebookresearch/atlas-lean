/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceIsIso

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (E : HomologyTheoryData.{w} C) [E.IsExact]
variable (k : ℤ) (P : TopPair.{w})

example (hSucc : IsZero ((E.Hₚ (k + 1)).obj P))
    (hSelf : IsZero ((E.Hₚ k).obj P)) :
    IsIso (E.subspaceMap k P) :=
  isIso_subspaceMap_of_isZero_relative E k P hSucc hSelf

example (hSucc : IsZero ((E.Hₚ (k + 1)).obj P))
    (hSelf : IsZero ((E.Hₚ k).obj P)) :
    (E.H k).obj P.snd ≅ (E.H k).obj P.fst := by
  let _ : IsIso (E.subspaceMap k P) :=
    isIso_subspaceMap_of_isZero_relative E k P hSucc hSelf
  exact asIso (E.subspaceMap k P)

example (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsZero ((E.H (k - 1)).obj P.snd)) :
    IsIso (E.toRelative k P) :=
  isIso_toRelative_of_isZero_subspace E k P hSelf hPrev

example (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsZero ((E.H (k - 1)).obj P.snd)) :
    (E.H k).obj P.fst ≅ (E.Hₚ k).obj P := by
  let _ : IsIso (E.toRelative k P) :=
    isIso_toRelative_of_isZero_subspace E k P hSelf hPrev
  exact asIso (E.toRelative k P)

end TopPair.HomologyTheoryData.IsExact
