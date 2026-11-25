/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoTripleSpan
public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointTransport

/-!
# Target comparison for admissible-mono triple spans

For the zero-based flag attached to `A₀ ↪ A₁ ↪ A₂ ↪ A₃`, the long interval
`[A₀,A₃]` is canonically isomorphic to the separately selected quotient of
the total composite.  The proof transports the selected admissible exact
sequence through named endpoint isomorphisms and a conjugation formula for
the long flag map; it does not rewrite dependently inside `ShortComplex.mk`.

Combining this with the source comparison transports the interval span to a
raw Quillen span between the selected source and target quotients.  Identity,
composition, quotient descent, functor, nerve, and realization claims remain
separate.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open AlgebraicKTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

theorem admissibleMonoTripleFlag_obj_one
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    (admissibleMonoTripleFlag f hf g hg h hh).chain.obj (1 : Fin 5) = A₀ :=
  rfl

theorem admissibleMonoTripleFlag_obj_four
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    (admissibleMonoTripleFlag f hf g hg h hh).chain.obj (4 : Fin 5) = A₃ :=
  rfl

/-- The long map in the triple flag is the threefold composite. -/
theorem admissibleMonoTripleFlag_map_one_four
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h)
    (h14 : (1 : Fin 5) ≤ (4 : Fin 5)) :
    (admissibleMonoTripleFlag f hf g hg h hh).chain.map
        (homOfLE h14) = (f ≫ g) ≫ h := by
  change (ComposableArrows.mk₃ f g h).map' 0 3 = (f ≫ g) ≫ h
  rw [ComposableArrows.map'_comp _ 0 2 3,
    ComposableArrows.map'_comp _ 0 1 2]
  rfl

/-- The target interval of the triple flag is the selected quotient of the
total composite. -/
noncomputable def admissibleMonoTripleTargetIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let F := admissibleMonoTripleFlag f hf g hg h hh
    let hfg := admissibleMonoTriple_comp_admissible f hf g hg h hh
    F.intervalQuotient (1 : Fin 5) (4 : Fin 5) (by decide) ≅
      admissibleMonoQuotient ((f ≫ g) ≫ h) hfg := by
  let F := admissibleMonoTripleFlag f hf g hg h hh
  let hfg := admissibleMonoTriple_comp_admissible f hf g hg h hh
  let h14 : (1 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h1 : F.chain.obj (1 : Fin 5) = A₀ :=
    admissibleMonoTripleFlag_obj_one f hf g hg h hh
  let h4 : F.chain.obj (4 : Fin 5) = A₃ :=
    admissibleMonoTripleFlag_obj_four f hf g hg h hh
  let e1 := eqToIso h1
  let e4 := eqToIso h4
  let m := F.chain.map (homOfLE h14)
  let c := (f ≫ g) ≫ h
  have hm : m = c :=
    admissibleMonoTripleFlag_map_one_four f hf g hg h hh h14
  have hconj : m = e1.hom ≫ c ≫ e4.inv := by
    change m = eqToHom h1 ≫ c ≫ eqToHom h4.symm
    exact (conj_eqToHom_iff_heq m c h1 h4).2 (heq_of_eq hm)
  let q := admissibleMonoQuotientπ c hfg
  let qFlag : F.chain.obj (4 : Fin 5) ⟶
      admissibleMonoQuotient c hfg := e4.hom ≫ q
  have hzero : c ≫ q = 0 :=
    comp_admissibleMonoQuotientπ c hfg
  have wFlag : m ≫ qFlag = 0 := by
    calc
      m ≫ qFlag = (e1.hom ≫ c ≫ e4.inv) ≫
          (e4.hom ≫ q) := by rw [hconj]
      _ = e1.hom ≫ (c ≫ q) := by simp [Category.assoc]
      _ = 0 := by rw [hzero, comp_zero]
  let Sflag : ShortComplex C := ShortComplex.mk m qFlag wFlag
  let Sselected : ShortComplex C :=
    ShortComplex.mk c q (comp_admissibleMonoQuotientπ c hfg)
  let eS : Sflag ≅ Sselected :=
    ShortComplex.isoMk e1 e4 (Iso.refl _) (by
      change e1.hom ≫ c = m ≫ e4.hom
      rw [hconj]
      simp) (by
      change e4.hom ≫ q = qFlag ≫ 𝟙 _
      simp [qFlag])
  have hSelected : IsAdmissibleExact Sselected :=
    admissibleMonoQuotient_exact c hfg
  have hFlag : IsAdmissibleExact Sflag :=
    isAdmissibleExact_of_iso eS.symm hSelected
  exact F.intervalIsoOfExact h14 qFlag wFlag hFlag

/-- The long-interval projection followed by the target comparison is the
selected quotient projection, transported from the literal last flag object. -/
@[reassoc (attr := simp)]
theorem admissibleMonoTripleTargetIso_projection
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let F := admissibleMonoTripleFlag f hf g hg h hh
    let hfg := admissibleMonoTriple_comp_admissible f hf g hg h hh
    let h4 := admissibleMonoTripleFlag_obj_four f hf g hg h hh
    F.intervalπ (1 : Fin 5) (4 : Fin 5) (by decide) ≫
        (admissibleMonoTripleTargetIso f hf g hg h hh).hom =
      (eqToIso h4).hom ≫
        admissibleMonoQuotientπ ((f ≫ g) ≫ h) hfg := by
  let F := admissibleMonoTripleFlag f hf g hg h hh
  let hfg := admissibleMonoTriple_comp_admissible f hf g hg h hh
  let h4 := admissibleMonoTripleFlag_obj_four f hf g hg h hh
  let h14 : (1 : Fin 5) ≤ (4 : Fin 5) := by decide
  unfold admissibleMonoTripleTargetIso
  exact F.intervalπ_intervalIsoOfExact_hom h14
    ((eqToIso h4).hom ≫
      admissibleMonoQuotientπ ((f ≫ g) ≫ h) hfg) _ _

/-- The triple quotient span transported to the selected source and target
quotient objects. -/
noncomputable def admissibleMonoTripleQuillenSpan
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let hfg := admissibleMonoTriple_comp_admissible f hf g hg h hh
    QuillenSpan (admissibleMonoQuotient g hg)
      (admissibleMonoQuotient ((f ≫ g) ≫ h) hfg) := by
  exact AlgebraicKTheory.QuillenSpan.endpointTransport
    (admissibleMonoTripleIntervalSpan f hf g hg h hh)
    (admissibleMonoTripleSourceIso f hf g hg h hh)
    (admissibleMonoTripleTargetIso f hf g hg h hh)

end CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

end
