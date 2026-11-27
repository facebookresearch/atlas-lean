/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Triangulated.ExceptionalGeneration

@[expose] public section

namespace CategoryTheory.Pretriangulated

open CategoryTheory CategoryTheory.Limits

universe w v u

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

-- Finite total `Hom` is finiteness of every graded piece and finiteness of the support.
example (A X : C) (h : HasFiniteTotalHom k A X) (n : ℤ) : Module.Finite k (A ⟶ X⟦n⟧) :=
  h.1 n

-- Empty family: if `Q` has no nonzero objects, every object of `Q` lies in every triangulated
-- subcategory, since it is zero.
example (Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ M : C, Q M → IsZero M)
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (M : C) (hM : Q M) : P M :=
  prop_of_hasFiniteTotalHom_of_exceptional k (Fin.elim0 : Fin 0 → C)
    (fun a ↦ a.elim0) (fun a ↦ a.elim0) (fun a ↦ a.elim0) (fun a ↦ a.elim0)
    Q (fun a ↦ a.elim0) (fun M hQM _ ↦ hQ M hQM) P (fun a ↦ a.elim0) M hM (fun a ↦ a.elim0)

-- One exceptional object `G` generating `Q`: objects of `Q` with finite total `Hom` from `G`
-- lie in every triangulated subcategory containing `G`.
example (G : C) (hG₀ : ∀ e : G ⟶ G, ∃ c : k, e = c • 𝟙 G)
    (hG₁ : ∀ n : ℤ, n ≠ 0 → Subsingleton (G ⟶ G⟦n⟧))
    (Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms] (hQG : Q G)
    (hgen : ∀ M : C, Q M → (∀ n : ℤ, Subsingleton (G ⟶ M⟦n⟧)) → IsZero M)
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (hPG : P G)
    (M : C) (hQM : Q M) (hM : HasFiniteTotalHom k G M) : P M :=
  prop_of_hasFiniteTotalHom_of_exceptional k (fun _ : Fin 1 ↦ G)
    (fun _ ↦ hG₀) (fun _ ↦ hG₁) (fun a b hab ↦ absurd hab (by omega))
    (fun a b hab ↦ absurd hab (by omega)) Q (fun _ ↦ hQG) (fun M hQM h ↦ hgen M hQM (h 0)) P
    (fun _ ↦ hPG) M hQM (fun _ ↦ hM)

end CategoryTheory.Pretriangulated
