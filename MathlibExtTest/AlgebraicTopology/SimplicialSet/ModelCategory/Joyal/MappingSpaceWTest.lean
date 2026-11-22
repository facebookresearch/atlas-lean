/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanRecognition

/-!
# Clients for categorical probes and mapping-space recognition

These clients exercise internal postcomposition, categorical equivalence
on functor probes, the probe predicate and its closure laws, and the
Whitehead assembly with its explicit homotopy-group hypotheses. The
complete downstream recognition theorem is also exercised at arbitrary
universes, including the actual right mapping-space map. The additional
hypotheses of the relative probe lemmas do not restrict that theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace MappingSpaceWTest

section CompleteRecognition

variable {X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
  {f : X ⟶ Y}

example : SSet.categoricalEquivalences f ↔ SSet.isDwyerKanEquivalence f :=
  SSet.categoricalEquivalences_iff_isDwyerKanEquivalence

example (hDK : SSet.isDwyerKanEquivalence f) : SSet.categoricalEquivalences f :=
  hDK.categoricalEquivalences

example (hf : SSet.categoricalEquivalences f) (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.realizationWeakEquivalences (SSet.mappingSpaceRight.map X a b f) :=
  hf.rightMappingSpaceMap_weak a b

end CompleteRecognition


section InternalPostcomposition

variable (K X : SSet.{u}) (φ ψ : X ⟶ X)

example :
    MonoidalClosed.uncurry (SSet.ihomPostcompositionMap K X) =
      MonoidalClosed.comp K X X :=
  SSet.uncurry_ihomPostcompositionMap K X

example :
    MonoidalClosed.curry' φ ≫ SSet.ihomPostcompositionMap K X =
      MonoidalClosed.curry' ((ihom K).map φ) :=
  SSet.curry'_comp_ihomPostcompositionMap K X φ

example :
    (SSet.ihomPostcompositionMap K X).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv X X φ) =
      SSet.ihomVertexEquiv ((ihom K).obj X) ((ihom K).obj X)
        ((ihom K).map φ) :=
  SSet.ihomPostcompositionMap_app_ihomVertexEquiv K X φ

example :
    (SSet.ihomPostcompositionMap K X).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv X X (𝟙 X)) =
      SSet.ihomVertexEquiv ((ihom K).obj X) ((ihom K).obj X)
        (𝟙 ((ihom K).obj X)) := by
  rw [SSet.ihomPostcompositionMap_app_ihomVertexEquiv, (ihom K).map_id]

example :
    (SSet.ihomPostcompositionMap K X).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv X X (φ ≫ ψ)) =
      SSet.ihomVertexEquiv ((ihom K).obj X) ((ihom K).obj X)
        ((ihom K).map φ ≫ (ihom K).map ψ) := by
  rw [SSet.ihomPostcompositionMap_app_ihomVertexEquiv, (ihom K).map_comp]

end InternalPostcomposition

section PostcompositionCategorical

variable {X Y : SSet.{u}} {f : X ⟶ Y} (K : SSet.{u})

example (h : SSet.HasHoInverse f) :
    SSet.HasHoInverse ((ihom K).map f) :=
  h.ihomMap K

example [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (hf : SSet.categoricalEquivalences f) :
    SSet.categoricalEquivalences ((ihom K).map f) :=
  hf.ihomMap K

example [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (hf : SSet.categoricalEquivalences f) :
    (SSet.mapHomotopyCategory ((ihom K).map f)).IsEquivalence :=
  hf.isEquivalence_mapHomotopyCategory_ihomMap K

example [SSet.Quasicategory X] :
    SSet.categoricalEquivalences ((ihom K).map (𝟙 X)) :=
  (SSet.categoricalEquivalences.of_isIso (𝟙 X)).ihomMap K

example (u : K ⟶ X) :
    (SSet.mapHomotopyCategory ((ihom K).map f)).obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X u)) =
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (u ≫ f)) :=
  SSet.mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv K u

end PostcompositionCategorical

section Probes

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example : SSet.dwyerKanFullyFaithfulProbes f ↔
    ∀ K : SSet.{u},
      (SSet.mapHomotopyCategory ((ihom K).map f)).Full ∧
        (SSet.mapHomotopyCategory ((ihom K).map f)).Faithful :=
  Iff.rfl

example [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (hf : SSet.categoricalEquivalences f) :
    SSet.dwyerKanFullyFaithfulProbes f :=
  hf.dwyerKanFullyFaithfulProbes

example : SSet.dwyerKanFullyFaithfulProbes (𝟙 X) :=
  SSet.dwyerKanFullyFaithfulProbes_id

example {C D : Type u} [Category.{u} C] [Category.{u} D]
    (e : Cat.of C ≅ Cat.of D) :
    SSet.dwyerKanFullyFaithfulProbes
      (CategoryTheory.nerveMap e.hom.toFunctor) :=
  (SSet.categoricalEquivalences.nerveMap_catIso_hom e)
    |>.dwyerKanFullyFaithfulProbes

example (h : SSet.dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) :
    (SSet.mapHomotopyCategory ((ihom K).map f)).FullyFaithful :=
  h.fullyFaithful K

-- Essential surjectivity does not follow from the probe
-- predicate alone; it holds for categorical equivalences via
-- the stronger equivalence theorem.
example [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (hf : SSet.categoricalEquivalences f) (K : SSet.{u}) :
    (SSet.mapHomotopyCategory ((ihom K).map f)).EssSurj := by
  have := hf.isEquivalence_mapHomotopyCategory_ihomMap K
  infer_instance

example (h : SSet.dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (a b : ((ihom K).obj X).HomotopyCategory) :
    Function.Bijective
      ((SSet.mapHomotopyCategory ((ihom K).map f)).map :
        (a ⟶ b) →
          ((SSet.mapHomotopyCategory ((ihom K).map f)).obj a ⟶
            (SSet.mapHomotopyCategory ((ihom K).map f)).obj b)) :=
  h.map_bijective K a b

example (h : SSet.dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (u v : K ⟶ X) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X u) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X v)) ≃
      (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (u ≫ f)) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (v ≫ f))) :=
  h.homEquivMk K u v

/--
warning: `SSet.dwyerKanFullyFaithfulProbes.homEquiv_mk` has been deprecated: Use `SSet.dwyerKanFullyFaithfulProbes.homEquivMk` instead
-/
#guard_msgs in
example (h : SSet.dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (a b : K ⟶ X) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X a) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X b)) ≃
      (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (a ≫ f)) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (b ≫ f))) :=
  h.homEquiv_mk K a b

example (h : SSet.dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (u v : K ⟶ X) :
    Function.Bijective (h.homEquivMk K u v) :=
  (h.homEquivMk K u v).bijective

end Probes

section EdgeForms

variable {X Y : SSet.{u}} {f : X ⟶ Y} (K : SSet.{u}) {u v : K ⟶ X}

example (h : SSet.dwyerKanFullyFaithfulProbes f)
    (e : SSet.Edge (SSet.ihomVertexEquiv K X u)
      (SSet.ihomVertexEquiv K X v)) :
    h.homEquivMk K u v e.toHoHom =
      ((e.map ((ihom K).map f)).ofEq
        (SSet.ihomVertexEquiv_ihom_map u f)
        (SSet.ihomVertexEquiv_ihom_map v f)).toHoHom :=
  h.homEquiv_mk_toHoHom K e

example [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (hf : SSet.categoricalEquivalences f)
    (e' : SSet.Edge (SSet.ihomVertexEquiv K Y (u ≫ f))
      (SSet.ihomVertexEquiv K Y (v ≫ f))) :
    ∃ e : SSet.Edge (SSet.ihomVertexEquiv K X u)
        (SSet.ihomVertexEquiv K X v),
      ((e.map ((ihom K).map f)).ofEq
        (SSet.ihomVertexEquiv_ihom_map u f)
        (SSet.ihomVertexEquiv_ihom_map v f)).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulProbes.exists_edge_map_ofEq_toHoHom_eq K e'

example (h : SSet.dwyerKanFullyFaithfulProbes f)
    {e₁ e₂ : SSet.Edge (SSet.ihomVertexEquiv K X u)
      (SSet.ihomVertexEquiv K X v)}
    (hh : ((e₁.map ((ihom K).map f)).ofEq
        (SSet.ihomVertexEquiv_ihom_map u f)
        (SSet.ihomVertexEquiv_ihom_map v f)).toHoHom =
      ((e₂.map ((ihom K).map f)).ofEq
        (SSet.ihomVertexEquiv_ihom_map u f)
        (SSet.ihomVertexEquiv_ihom_map v f)).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  h.edge_map_ofEq_toHoHom_injective K hh

end EdgeForms

section ProbeClosure

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {g' : Y ⟶ X}

example (hf : SSet.dwyerKanFullyFaithfulProbes f)
    (hg : SSet.dwyerKanFullyFaithfulProbes g) :
    SSet.dwyerKanFullyFaithfulProbes (f ≫ g) :=
  hf.comp hg

example (hfg : SSet.dwyerKanFullyFaithfulProbes (f ≫ g'))
    (hgf : SSet.dwyerKanFullyFaithfulProbes (g' ≫ f)) :
    SSet.dwyerKanFullyFaithfulProbes f :=
  SSet.dwyerKanFullyFaithfulProbes.of_comp_comp hfg hgf

example (hfg : SSet.dwyerKanFullyFaithfulProbes (f ≫ g'))
    (hgf : SSet.dwyerKanFullyFaithfulProbes (g' ≫ f)) :
    SSet.dwyerKanFullyFaithfulProbes g' :=
  SSet.dwyerKanFullyFaithfulProbes.of_comp_comp hgf hfg

example (hfg : SSet.dwyerKanFullyFaithfulProbes (f ≫ g'))
    (hgf : SSet.dwyerKanFullyFaithfulProbes (g' ≫ f)) (K : SSet.{u})
    (u v : K ⟶ X) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X u) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X v)) ≃
      (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (u ≫ f)) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (v ≫ f))) :=
  (SSet.dwyerKanFullyFaithfulProbes.of_comp_comp hfg hgf).homEquivMk
    K u v

end ProbeClosure

section WhiteheadAssembly

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective
        (SSet.mapπ₀ (SSet.mappingSpaceRight.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (SSet.mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (SSet.KanComplex.π.map (SSet.mappingSpaceRight.map X a b f)
          rfl (n := n + 1) (x := σ))) :
    SSet.dwyerKanFullyFaithful f :=
  SSet.dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap hKanX
    hKanY h₀ hπ

example (hKan : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b)) :
    SSet.dwyerKanFullyFaithful (𝟙 X) := by
  apply SSet.dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap
    hKan
  · intro a b
    simpa using hKan a b
  · intro a b
    have : SSet.KanComplex (SSet.mappingSpaceRight X a b) := hKan a b
    rw [SSet.mappingSpaceRight.map_id]
    exact (SSet.KanComplex.W.id
      (X := SSet.mappingSpaceRight X a b)).bijective_mapπ₀
  · intro a b n σ
    have : SSet.KanComplex (SSet.mappingSpaceRight X a b) := hKan a b
    rw [SSet.mappingSpaceRight.map_id]
    exact (SSet.KanComplex.W.id
      (X := SSet.mappingSpaceRight X a b)).bijective_piMap (n + 1) σ

example (hf : SSet.categoricalEquivalences f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective
        (SSet.mapπ₀ (SSet.mappingSpaceRight.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (SSet.mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (SSet.KanComplex.π.map (SSet.mappingSpaceRight.map X a b f)
          rfl (n := n + 1) (x := σ))) :
    SSet.isDwyerKanEquivalence f :=
  hf.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap hKanX hKanY
    h₀ hπ

end WhiteheadAssembly

section UniverseZero

variable {X Y : SSet.{0}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
  {f : X ⟶ Y}

example (hf : SSet.categoricalEquivalences.{0} f) :
    SSet.dwyerKanFullyFaithfulProbes f :=
  hf.dwyerKanFullyFaithfulProbes

example (hf : SSet.categoricalEquivalences.{0} f) (K : SSet.{0})
    (u v : K ⟶ X) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X u) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K X v)) ≃
      (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (u ≫ f)) ⟶
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv K Y (v ≫ f))) :=
  hf.dwyerKanFullyFaithfulProbes.homEquivMk K u v

example (hf : SSet.categoricalEquivalences.{0} f) (K : SSet.{0})
    {u v : K ⟶ X}
    (e' : SSet.Edge (SSet.ihomVertexEquiv K Y (u ≫ f))
      (SSet.ihomVertexEquiv K Y (v ≫ f))) :
    ∃ e : SSet.Edge (SSet.ihomVertexEquiv K X u)
        (SSet.ihomVertexEquiv K X v),
      ((e.map ((ihom K).map f)).ofEq
        (SSet.ihomVertexEquiv_ihom_map u f)
        (SSet.ihomVertexEquiv_ihom_map v f)).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulProbes.exists_edge_map_ofEq_toHoHom_eq K e'

end UniverseZero

end MappingSpaceWTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
