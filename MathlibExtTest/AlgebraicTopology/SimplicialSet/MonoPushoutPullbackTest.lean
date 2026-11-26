/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoPushoutPullback

public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace MonoPushoutPullbackTest

private theorem original_full_contract {A X A' X' B Y : SSet.{u}}
    {i : A ⟶ X} {p : A ⟶ A'} {f : X ⟶ X'} {i' : A' ⟶ X'}
    {j : A' ⟶ B} {q : X' ⟶ Y} {k : B ⟶ Y}
    [Mono i] [Mono k]
    (top : IsPushout i p f i') (bot : CommSq i' j q k)
    (outer : IsPullback i (p ≫ j) (f ≫ q) k) : IsPullback i' j q k :=
  SSet.RezkMonoPushout.isPullback_tail top bot outer

private theorem original_middle_mono {A X A' X' : SSet.{u}}
    {i : A ⟶ X} {p : A ⟶ A'} {f : X ⟶ X'} {i' : A' ⟶ X'}
    [Mono i] (top : IsPushout i p f i') : Mono i' :=
  Adhesive.mono_of_isPushout_of_mono_left top

private theorem original_full_outer_again {A X A' X' B Y : SSet.{u}}
    {i : A ⟶ X} {p : A ⟶ A'} {f : X ⟶ X'} {i' : A' ⟶ X'}
    {j : A' ⟶ B} {q : X' ⟶ Y} {k : B ⟶ Y}
    [Mono i] [Mono k]
    (top : IsPushout i p f i') (bot : CommSq i' j q k)
    (outer : IsPullback i (p ≫ j) (f ≫ q) k) :
    IsPullback i (p ≫ j) (f ≫ q) k :=
  (Adhesive.isPullback_of_isPushout_of_mono_left top).paste_vert
    (SSet.RezkMonoPushout.isPullback_tail top bot outer)

end MonoPushoutPullbackTest
