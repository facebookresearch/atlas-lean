/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cup
import Mathlib.Tactic.FinCases

/-!
# Tests for the cup product of Čech cochains

The front and back faces overlap in one vertex (Alexander–Whitney), and the cup product carries
no sign: the cup product of the cochains given by restricting two global sections is the cochain
given by restricting their product, in every bidegree.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace OrderedAffineCoverCupTest

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
  (K : V.OrderedAffineCover)

/-- In bidegree `(1, 1)` the front and back faces of `(s₀, s₁, s₂)` are `(s₀, s₁)` and
`(s₁, s₂)`. -/
example (s : K.Idx 2) :
    (K.frontFace 1 1 2 rfl s).1 = ![s.1 0, s.1 1] ∧
      (K.backFace 1 1 2 rfl s).1 = ![s.1 1, s.1 2] :=
  ⟨funext fun j => by fin_cases j <;> rfl, funext fun j => by fin_cases j <;> rfl⟩

/-- The structure-sheaf cochain given by restricting a global section `g` to each intersection. -/
private def restrictGlobal (g : Γ(V, ⊤)) (a : ℕ) : (OModulePresheaf.unit π).cochain K a :=
  fun t => (V.presheaf.map (homOfLE (le_top : K.inter t ≤ ⊤)).op).hom g

private theorem map_map_global {W W' : V.Opens} (e : W ≤ W') (e' : W' ≤ ⊤) (x : Γ(V, ⊤)) :
    (V.presheaf.map (homOfLE e).op).hom ((V.presheaf.map (homOfLE e').op).hom x) =
      (V.presheaf.map (homOfLE (e.trans e')).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- No sign: the cup product of the restrictions of `g` and `h` is the restriction of `g * h`. -/
example (a b n : ℕ) (hab : a + b = n) (g h : Γ(V, ⊤)) (s : K.Idx n) :
    (OModulePresheaf.unit π).cup K a b n hab (restrictGlobal K g a) (restrictGlobal K h b) s =
      restrictGlobal K (g * h) n s := by
  change (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n hab s)).op).hom
        ((V.presheaf.map (homOfLE le_top).op).hom g) *
      (V.presheaf.map (homOfLE (K.inter_le_inter_backFace a b n hab s)).op).hom
        ((V.presheaf.map (homOfLE le_top).op).hom h) =
    (V.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op).hom (g * h)
  rw [map_map_global, map_map_global, ← map_mul]

end OrderedAffineCoverCupTest
