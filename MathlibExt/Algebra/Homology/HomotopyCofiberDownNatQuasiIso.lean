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

public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntExact
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomotopyCofiber
public import MathlibExt.Algebra.Homology.HomotopyCofiberQuasiIso

/-!
# Quasi-isomorphisms of cofibers of nonnegative chain complexes

In an abelian category C, a commuting square between maps of nonnegative
chain complexes whose two vertical maps are quasi-isomorphisms induces a
quasi-isomorphism of their homotopy cofibers. The cofiber map uses the
predecessor n+1 of each degree n for the descending chain shape.

For a short exact sequence K → L → M of nonnegative chain complexes,
the canonical map from the cofiber of K → L to M is a quasi-isomorphism.
The cofiber of the forward map of a homotopy equivalence is therefore
acyclic in all nonnegative degrees.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe v u

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem downNatHasPrev :
    ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j :=
  fun j ↦ ⟨j + 1, by simp⟩

private theorem downIntHasPrev :
    ∀ j : ℤ, ∃ i, (ComplexShape.down ℤ).Rel i j :=
  fun j ↦ ⟨j + 1, by simp⟩

/-- Let C be abelian and let a:K → K′, b:L → L′ form a commuting square
between nonnegative chain maps f:K → L and g:K′ → L′.
If a and b are quasi-isomorphisms, the induced map
Cofib(f) → Cofib(g), using the chain-shape predecessors n+1,
is a quasi-isomorphism. -/
theorem quasiIso_mapArrowHom_downNat
    {K L K' L' : ChainComplex C ℕ} {f : K ⟶ L} {g : K' ⟶ L'}
    (a : Arrow.mk f ⟶ Arrow.mk g)
    (ha : QuasiIso a.left) (hb : QuasiIso a.right) :
    QuasiIso
      (HomologicalComplex.homotopyCofiber.mapArrowHom
        f g (fun j : ℕ ↦ ⟨j + 1, by simp⟩) a) := by
  rw [show (fun j : ℕ ↦ ⟨j + 1, by simp⟩) = downNatHasPrev from
    Subsingleton.elim _ _]
  let e := ComplexShape.embeddingDownNatToInt
  let aInt := (e.extendFunctor C).mapArrow.map a
  have haInt : QuasiIso (HomologicalComplex.extendMap a.left e) :=
    (quasiIso_extendDownNatToInt_iff a.left).2 ha
  have hbInt : QuasiIso (HomologicalComplex.extendMap a.right e) :=
    (quasiIso_extendDownNatToInt_iff a.right).2 hb
  let middle := HomologicalComplex.homotopyCofiber.mapArrowHom
    (HomologicalComplex.extendMap f e)
    (HomologicalComplex.extendMap g e)
    downIntHasPrev aInt
  have hmiddle : QuasiIso middle :=
    HomologicalComplex.homotopyCofiber.quasiIso_mapArrowHom
      aInt haInt hbInt
  have htransport : QuasiIso
      ((HomologicalComplex.homotopyCofiber.extendIso f e).inv ≫
        middle ≫
        (HomologicalComplex.homotopyCofiber.extendIso g e).hom) :=
    quasiIso_comp _ _ (hφ := inferInstance)
      (hφ' := quasiIso_comp _ _
        (hφ := hmiddle) (hφ' := inferInstance))
  have hext : QuasiIso
      (HomologicalComplex.extendMap
        (HomologicalComplex.homotopyCofiber.mapArrowHom
          (Arrow.mk f).hom (Arrow.mk g).hom downNatHasPrev a) e) := by
    have heta : Arrow.homMk' a.left a.right (w := a.w) = a := by
      ext <;> rfl
    rw [← heta]
    rw [HomologicalComplex.homotopyCofiber.extendMap_mapArrowHom
      e downNatHasPrev downIntHasPrev a]
    exact htransport
  exact (quasiIso_extendDownNatToInt_iff _).1 hext

/-- In an abelian category C, for a short exact sequence
K —f→ L —g→ M of nonnegative chain complexes, the canonical
cofiber map Cofib(f) → M induced by g and g∘f=0 is a
quasi-isomorphism. -/
theorem quasiIso_descShortComplex_downNat
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) :
    QuasiIso
      (HomologicalComplex.homotopyCofiber.descShortComplex S) := by
  let e := ComplexShape.embeddingDownNatToInt
  let Se := S.map (e.extendFunctor C)
  have hSInt : Se.ShortExact := by
    simpa only [Se, e,
      ComplexShape.embeddingDownNatToIntExtendFunctor] using
      (ShortComplex.ShortExact.map_embeddingDownNatToIntExtend S hS)
  have hdesc : QuasiIso
      (HomologicalComplex.homotopyCofiber.descShortComplex Se) :=
    HomologicalComplex.homotopyCofiber.quasiIso_descShortComplex Se hSInt
  have htransport : QuasiIso
      ((HomologicalComplex.homotopyCofiber.extendIso S.f e).inv ≫
        HomologicalComplex.homotopyCofiber.descShortComplex Se) :=
    quasiIso_comp _ _ (hφ := inferInstance) (hφ' := hdesc)
  have hext : QuasiIso
      (HomologicalComplex.extendMap
        (HomologicalComplex.homotopyCofiber.descShortComplex S) e) := by
    rw [HomologicalComplex.homotopyCofiber.extendMap_descShortComplex e S]
    exact htransport
  exact (quasiIso_extendDownNatToInt_iff
    (HomologicalComplex.homotopyCofiber.descShortComplex S)).1 hext

end HomologicalComplex.homotopyCofiber

namespace HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category C, if e is a homotopy equivalence between
nonnegative chain complexes K and L, the homotopy cofiber of its
forward map e:K → L is acyclic in every nonnegative degree. -/
theorem homotopyCofiber_acyclic
    {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    (HomologicalComplex.homotopyCofiber e.hom).Acyclic := by
  let Z : ChainComplex C ℕ := HomologicalComplex.zero
  let S : ShortComplex (ChainComplex C ℕ) :=
    ShortComplex.mk (𝟙 L) (0 : L ⟶ Z) (by simp)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk'
      ((S.exact_iff_epi (by rfl)).2 ?_) ?_ ?_
    · dsimp only [S]
      infer_instance
    · dsimp only [S]
      infer_instance
    · have hZ : IsZero Z := by
        dsimp only [Z]
        exact HomologicalComplex.isZero_zero
      exact hZ.epi S.g
  let a : Arrow.mk e.hom ⟶ Arrow.mk (𝟙 L) :=
    Arrow.homMk' e.hom (𝟙 L) (by simp)
  have haRight : QuasiIso a.right := by
    change QuasiIso (𝟙 L)
    infer_instance
  have hcone : QuasiIso
      (HomologicalComplex.homotopyCofiber.mapArrowHom
        e.hom (𝟙 L) (fun j : ℕ ↦ ⟨j + 1, by simp⟩) a) :=
    HomologicalComplex.homotopyCofiber.quasiIso_mapArrowHom_downNat
      a e.quasiIso_hom haRight
  have hdesc : QuasiIso
      (HomologicalComplex.homotopyCofiber.descShortComplex S) :=
    HomologicalComplex.homotopyCofiber.quasiIso_descShortComplex_downNat
      S hS
  let q : HomologicalComplex.homotopyCofiber e.hom ⟶
      (HomologicalComplex.zero : ChainComplex C ℕ) :=
    HomologicalComplex.homotopyCofiber.mapArrowHom
        e.hom (𝟙 L) (fun j : ℕ ↦ ⟨j + 1, by simp⟩) a ≫
      HomologicalComplex.homotopyCofiber.descShortComplex S
  have hq : QuasiIso q := by
    dsimp only [q]
    exact quasiIso_comp _ _ (hφ := hcone) (hφ' := hdesc)
  intro n
  exact (quasiIsoAt_iff_exactAt' q n
    ((HomologicalComplex.acyclic_of_isZero HomologicalComplex.zero
      HomologicalComplex.isZero_zero) n)).mp (hq.quasiIsoAt n)

end HomotopyEquiv

end
