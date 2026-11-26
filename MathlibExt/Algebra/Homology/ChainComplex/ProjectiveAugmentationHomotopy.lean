/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Uniqueness of projective lifts through a quasi-isomorphism

Let C be abelian and let P,Q,T be natural-number-indexed chain complexes. If every Pₙ is
projective and q : Q → T is a quasi-isomorphism, then two chain maps f,g : P → Q satisfying q ∘
f = q ∘ g are homotopic. Hence their maps on every homology object agree. No projectivity of Q
or T is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {P Q T : ChainComplex C ℕ} [∀ n, Projective (P.X n)]

/-- Let C be an abelian category. Let P,Q,T be chain complexes indexed by ℕ, and assume every Pₙ is
projective. For a quasi-isomorphism q : Q → T and maps f,g : P → Q with q ∘ f=q ∘ g, there is a
chain homotopy f ≃ g. The terms of Q and T need not be projective. -/
def projectiveHomotopyOfCompQuasiIso
    (q : Q ⟶ T) (hq : QuasiIso q) (f g : P ⟶ Q)
    (h : f ≫ q = g ≫ q) : Homotopy f g := by
  let _ := HasDerivedCategory.standard C
  let e := ComplexShape.embeddingDownNat
  let E := e.extendFunctor C
  let U := HomotopyCategory.quotient C (.up ℤ)
  let D := DerivedCategory.Qh (C := C)
  let _ : CochainComplex.IsKProjective (E.obj P) :=
    inferInstanceAs (CochainComplex.IsKProjective (P.extend ComplexShape.embeddingDownNat))
  have hq' : QuasiIso (E.map q) :=
    (HomologicalComplex.quasiIso_extendMap_iff q e).2 hq
  let _ : IsIso (D.map (U.map (E.map q))) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) (E.map q)).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C (E.map q)).2 hq')
  have hD : D.map (U.map (E.map f)) = D.map (U.map (E.map g)) := by
    apply (cancel_mono (D.map (U.map (E.map q)))).1
    rw [← D.map_comp, ← D.map_comp, ← U.map_comp, ← U.map_comp,
      ← E.map_comp, ← E.map_comp, h]
  have hU : U.map (E.map f) = U.map (E.map g) :=
    (CochainComplex.IsKProjective.Qh_map_bijective (E.obj P) (U.obj (E.obj Q))).injective hD
  exact (HomotopyCategory.homotopyOfEq (E.map f) (E.map g) hU).ofExtend

/-- Let C be an abelian category. Let P,Q,T be ℕ-indexed chain complexes with every Pₙ projective.
If q : Q → T is a quasi-isomorphism and f,g : P → Q satisfy q ∘ f=q ∘ g, then Hₙ(f)=Hₙ(g) for
every n ∈ ℕ, by the resulting homotopy. -/
theorem homologyMap_eq_of_comp_quasiIso
    (q : Q ⟶ T) (hq : QuasiIso q) (f g : P ⟶ Q)
    (h : f ≫ q = g ≫ q) (n : ℕ) :
    HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n :=
  (projectiveHomotopyOfCompQuasiIso q hq f g h).homologyMap_eq n

end ChainComplex
