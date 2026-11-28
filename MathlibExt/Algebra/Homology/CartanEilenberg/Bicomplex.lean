/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Basic
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# The Cartan–Eilenberg bicomplex

Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. The chosen
resolutions Rⱼ of the terms Lⱼ have lifted chain maps Dⱼ : Rⱼ₊₁ → Rⱼ covering d_L^{j+1,j}. The
maps factor through the boundary and cycles horseshoes and satisfy Dⱼ ∘ Dⱼ₊₁=0.

These resolutions form a chain complex of chain complexes. Its flipped bicomplex has first index
the resolution degree a, second index the original degree j, and entry Rⱼ,ₐ. Every entry is
projective.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

namespace CartanEilenbergResolution

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For every
j ∈ ℕ, the original differential Lⱼ₊₁ → Lⱼ lifts to a chain map Dⱼ : Rⱼ₊₁.complex → Rⱼ.complex
between the stored term resolutions. -/
noncomputable def termDifferential (j : ℕ) :
    (P.termResolution (j + 1)).complex ⟶
      (P.termResolution j).complex :=
  (P.termHorseshoe (j + 1)).p ≫
    (P.cyclesHorseshoe j).i ≫
    (P.termHorseshoe j).i

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
lifted map Dⱼ projects Rⱼ₊₁ to the resolution of its outgoing boundary, includes that boundary
resolution in Cⱼ, and then includes Cⱼ in Rⱼ. This three-map composite is the chosen term
differential. -/
@[reassoc]
theorem termDifferential_eq (j : ℕ) :
    P.termDifferential j =
      (P.termHorseshoe (j + 1)).p ≫
        (P.cyclesHorseshoe j).i ≫
        (P.termHorseshoe j).i :=
  rfl

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
consecutive lifted differentials satisfy Dⱼ ∘ Dⱼ₊₁=0 as chain maps of projective term
resolutions. -/
@[reassoc]
theorem termDifferential_comp (j : ℕ) :
    P.termDifferential (j + 1) ≫ P.termDifferential j = 0 := by
  simp only [termDifferential, Category.assoc]
  rw [← Category.assoc (P.termHorseshoe (j + 1)).i]
  rw [(P.termHorseshoe (j + 1)).zero]
  simp

private theorem baseDifferential (j : ℕ) :
    factorThruImage (L.dFrom (j + 1)) ≫
        L.boundaryToCycles j ≫ L.iCycles j =
      L.d (j + 1) j := by
  rw [← Category.assoc, L.factor_boundaryToCycles j]
  exact L.toCycles_i (j + 1) j

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. If πⱼ :
Rⱼ.complex → Lⱼ[0] are the stored augmentations, then πⱼ ∘ Dⱼ = (d_L^{j+1,j})[0] ∘ πⱼ₊₁. Thus Dⱼ
covers the original chain differential. -/
@[reassoc]
theorem termDifferential_comp_π (j : ℕ) :
    P.termDifferential j ≫ (P.termResolution j).π =
      (P.termResolution (j + 1)).π ≫
        (ChainComplex.single₀ C).map (L.d (j + 1) j) := by
  let A := P.termHorseshoe (j + 1)
  let B := P.cyclesHorseshoe j
  let D := P.termHorseshoe j
  have hA := A.p_augmentation
  have hB := B.i_augmentation
  have hD := D.i_augmentation
  change A.p ≫ (P.boundaryResolution (j + 1)).π =
      A.middle.π ≫
        (ChainComplex.single₀ C).map
          (factorThruImage (L.dFrom (j + 1))) at hA
  change B.i ≫ B.middle.π =
      (P.boundaryResolution (j + 1)).π ≫
        (ChainComplex.single₀ C).map (L.boundaryToCycles j) at hB
  change D.i ≫ D.middle.π =
      B.middle.π ≫
        (ChainComplex.single₀ C).map (L.iCycles j) at hD
  change (A.p ≫ B.i ≫ D.i) ≫ D.middle.π =
    A.middle.π ≫ (ChainComplex.single₀ C).map (L.d (j + 1) j)
  simp only [Category.assoc]
  rw [hD]
  rw [reassoc_of% hB]
  rw [reassoc_of% hA]
  rw [← Functor.map_comp, ← Functor.map_comp, baseDifferential]

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For each
j, the lifted term differential Dⱼ together with its augmentation square is a morphism of
projective resolutions over d_L^{j+1,j} : Lⱼ₊₁ → Lⱼ. -/
noncomputable def termDifferentialHom (j : ℕ) :
    ProjectiveResolution.Hom
      (P.termResolution (j + 1)) (P.termResolution j)
      (L.d (j + 1) j) where
  hom := P.termDifferential j
  hom_f_zero_comp_π_f_zero := by
    have h := HomologicalComplex.congr_hom
      (P.termDifferential_comp_π j) 0
    simpa only [HomologicalComplex.comp_f,
      ChainComplex.single₀_map_f_zero] using h

@[simp]
theorem termDifferentialHom_hom (j : ℕ) :
    (P.termDifferentialHom j).hom = P.termDifferential j :=
  rfl

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
term-resolution complexes Rⱼ.complex and their lifted maps Dⱼ form a chain complex indexed by
original degree j, with values in the category of nonnegative chain complexes. -/
noncomputable def termComplex :
    ChainComplex (ChainComplex C ℕ) ℕ :=
  ChainComplex.of
    (fun j => (P.termResolution j).complex)
    (fun j => P.termDifferential j)
    (fun j => P.termDifferential_comp j)

@[simp]
theorem termComplex_X (j : ℕ) :
    (P.termComplex).X j = (P.termResolution j).complex :=
  rfl

@[simp]
theorem termComplex_d (j : ℕ) :
    (P.termComplex).d (j + 1) j = P.termDifferential j := by
  unfold termComplex
  exact ChainComplex.of_d
    (fun k => (P.termResolution k).complex)
    (fun k => P.termDifferential k) j

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. Flipping
the two indices of this chain complex gives the Cartan–Eilenberg bicomplex, with entry
(a,j)=Rⱼ.complexₐ. Its first axis is resolution degree a and its second is original chain degree
j, both with down-ℕ shape. -/
noncomputable def bicomplex :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip P.termComplex

@[simp]
theorem bicomplex_X (a j : ℕ) :
    ((P.bicomplex.X a).X j) =
      (P.termResolution j).complex.X a :=
  rfl

@[simp]
theorem bicomplex_d₁ (a j : ℕ) :
    (P.bicomplex.d (a + 1) a).f j =
      (P.termResolution j).complex.d (a + 1) a :=
  rfl

@[simp]
theorem bicomplex_d₂ (a j : ℕ) :
    (P.bicomplex.X a).d (j + 1) j =
      (P.termDifferential j).f a := by
  change (P.termComplex.d (j + 1) j).f a = _
  rw [P.termComplex_d j]

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For every
pair a,j ∈ ℕ, the entry Rⱼ.complexₐ of the Cartan–Eilenberg bicomplex is a projective object of
C. -/
theorem bicomplex_projective (a j : ℕ) :
    Projective ((P.bicomplex.X a).X j) := by
  change Projective ((P.termResolution j).complex.X a)
  infer_instance

end CartanEilenbergResolution

end HomologicalComplex

end
