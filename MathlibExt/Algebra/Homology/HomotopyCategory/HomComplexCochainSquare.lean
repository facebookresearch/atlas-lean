/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Cochain-level chain-map naturality and square identities

Category-generic cochain lemmas over any `[Category C] [Preadditive C]`:

* `ofHom_comp_diff`: every cochain-complex morphism commutes with the
  differential cochain.
* `ofHom_comp_of_eq`: a chain-map composition equality promotes directly to
  an equality of degree-zero cochains, with a flexible degree witness.
* `diff_sq`: the differential cochain of any cochain complex composes with
  itself to zero, from `HomologicalComplex.d_comp_d`.
* `add_comp_self`: the square of a sum of degree-`1` endo-cochains expands as
  `(f + g).comp (f + g) = (f.comp f + f.comp g) + (g.comp f + g.comp g)`,
  from bilinearity of `Cochain.comp` (`Cochain.add_comp` / `Cochain.comp_add`).

These generalize the `ModuleCat` versions used by the Bar/Cobar total-square
leaves. No monoidal structure, ring, or module category is needed.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

namespace HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Cochain form of differential naturality: every morphism of cochain
complexes commutes with the differential cochain. -/
public theorem ofHom_comp_diff {F G : CochainComplex C ℤ} (f : F ⟶ G) :
    (ofHom f).comp (diff G) (zero_add 1) =
      (diff F).comp (ofHom f) (add_zero 1) := by
  apply ext
  intro r s hrs
  simp only [zero_cochain_comp_v, comp_zero_cochain_v, ofHom_v, diff_v]
  exact HomologicalComplex.Hom.comm f r s

/-- Promote an equality of complex morphisms whose left-hand side is a
composition to the corresponding equality of degree-zero cochains. The
degree witness is flexible, so either either canonical proof of
`0 + 0 = 0`. -/
public theorem ofHom_comp_of_eq {F G K : CochainComplex C ℤ}
    {f : F ⟶ G} {g : G ⟶ K} {h : F ⟶ K} (e : f ≫ g = h)
    (w : (0 : ℤ) + 0 = 0) :
    (ofHom f).comp (ofHom g) w = ofHom h := by
  rw [← ofHom_comp, e]

/-- Cochain-level internal square-zero: the differential cochain of any
cochain complex composes with itself to zero. -/
public theorem diff_sq (K : CochainComplex C ℤ) (h : (1 : ℤ) + 1 = 2) :
    (diff K).comp (diff K) h = 0 := by
  refine ext _ _ ?_
  intro p q hpq
  simp only [comp_v _ _ h p _ q rfl (by omega), diff_v, zero_v]
  exact HomologicalComplex.d_comp_d K p (p + 1) q

/-- `(2,0)+(1,1)+(0,2)` decomposition: the square of a sum of degree-`1`
endo-cochains expands by bilinearity of `Cochain.comp`. -/
public theorem add_comp_self (X : CochainComplex C ℤ)
    (f g : Cochain X X 1) (h : (1 : ℤ) + 1 = 2) :
    (f + g).comp (f + g) h =
      (f.comp f h + f.comp g h) + (g.comp f h + g.comp g h) := by
  rw [CochainComplex.HomComplex.Cochain.add_comp,
    CochainComplex.HomComplex.Cochain.comp_add,
    CochainComplex.HomComplex.Cochain.comp_add]

end HomComplex.Cochain

end CochainComplex
