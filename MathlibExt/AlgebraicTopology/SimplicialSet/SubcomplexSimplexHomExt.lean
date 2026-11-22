/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexHornAttachment

/-!
# Maps on a subcomplex and one attached original simplex

Agreement on the original subcomplex and on the entire attached simplex
implies agreement on their union. The proof reads the literal two
membership cases and retains the supplied simplex classifying map.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Maps on an original simplex attachment are determined by the old subcomplex and that whole simplex. -/
theorem Subcomplex.hom_ext_sup_of_simplex
    {Z W : SSet.{u}} {S : Z.Subcomplex} {m : ℕ}
    {z : Z.obj (op (SimplexCategory.mk m))}
    {f g : ((S ⊔ Subcomplex.ofSimplex z : Z.Subcomplex) : SSet.{u}) ⟶ W}
    (hS : Subcomplex.homOfLE (show S ≤ S ⊔ Subcomplex.ofSimplex z from
      le_sup_left) ≫ f =
        Subcomplex.homOfLE (show S ≤ S ⊔ Subcomplex.ofSimplex z from
          le_sup_left) ≫ g)
    (hz : S.simplexLiftSup z ≫ f = S.simplexLiftSup z ≫ g) :
    f = g := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, hxSup⟩
  have hx := hxSup
  rw [Subfunctor.max_obj] at hx
  rcases hx with hx | hx
  · let xS : S.obj d := ⟨x, hx⟩
    have hinc : (Subcomplex.homOfLE (show S ≤
          S ⊔ Subcomplex.ofSimplex z from le_sup_left)).app d xS =
        (⟨x, hxSup⟩ : (S ⊔ Subcomplex.ofSimplex z).obj d) := by
      apply Subtype.ext
      rfl
    simpa only [NatTrans.comp_app, types_comp_apply, hinc] using
      congr($(hS).app d xS)
  · have heq : Subcomplex.ofSimplex z =
        Subcomplex.range (yonedaEquiv.symm z) := by
      rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
    rw [heq, Subfunctor.range_obj] at hx
    obtain ⟨s, hs⟩ := hx
    have hinc : (S.simplexLiftSup z).app d s =
        (⟨x, hxSup⟩ : (S ⊔ Subcomplex.ofSimplex z).obj d) := by
      apply Subtype.ext
      exact hs
    simpa only [NatTrans.comp_app, types_comp_apply, hinc] using
      congr($(hz).app d s)


end SSet
