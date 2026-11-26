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
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Homology composition from a cochain-map comparison

Let C be an abelian category with independent object and morphism universes u,v. For nonnegative
cochain complexes A,B,D and maps e:A→B, f:B→D, t:A→D with e≫f=t, homology functoriality gives
H^n(e)≫H^n(f)=H^n(t).

A specified tail map τ:H^n(B)→H^n(D) equal to H^n(f) therefore satisfies H^n(e)≫τ=H^n(t). The
construction records this equality as lifted proof data.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be an abelian category in object and morphism universes u,v, and A,B,D nonnegative cochain
complexes. For e:A→B, f:B→D, t:A→D, and n≥0, suppose e≫f=t and τ:H^n(B)→H^n(D) equals H^n(f).
Then H^n(e)≫τ=H^n(t), provided as lifted proof data. -/
def liftedTailComposition {A B D : CochainComplex C ℕ}
    (e : A ⟶ B) (f : B ⟶ D) (t : A ⟶ D) (n : ℕ)
    (tail : B.homology n ⟶ D.homology n)
    (htail : tail = homologyMap f n) (hcomp : e ≫ f = t) :
    PLift (homologyMap e n ≫ tail = homologyMap t n) := by
  refine ⟨?_⟩
  rw [htail, ← homologyMap_comp, hcomp]

end HomologicalComplex
