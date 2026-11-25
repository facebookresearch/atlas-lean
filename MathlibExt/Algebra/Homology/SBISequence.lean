/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Natural-number indexed SBI diagrams

This file packages the diagram underlying a connective SBI sequence.  The
diagram, its exactness, and its connective boundary conditions are separate:
morphisms can therefore be constructed and composed before exactness is
proved.

For every `n`, the relevant five-term window is

```text
HC (n + 1) --B--> H (n + 2) --I--> HC (n + 2) --S--> HC n --B--> H (n + 1).
```

The comparison theorem only uses ordinary-homology maps through the requested
degree.  A convenience corollary accepts isomorphisms in every degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ComposableArrows

noncomputable section

universe w u

namespace CategoryTheory

open Limits

section ZeroMorphisms

variable {A : Type u} [Category.{w} A] [HasZeroMorphisms A]

/-- The diagram underlying a natural-number indexed SBI sequence.

Exactness and the connective boundary conditions are separate properties;
see `NatSBIDiagram.Exact` and `NatSBIDiagram.ConnectiveBoundary`. -/
structure NatSBIDiagram where
  /-- The ordinary homology family. -/
  H : ℕ → A
  /-- The cyclic-type homology family. -/
  HC : ℕ → A
  /-- Inclusion from ordinary to cyclic-type homology. -/
  I : ∀ n : ℕ, H n ⟶ HC n
  /-- Periodicity map. -/
  S : ∀ n : ℕ, HC (n + 2) ⟶ HC n
  /-- Connecting map. -/
  B : ∀ n : ℕ, HC n ⟶ H (n + 1)
  S_comp_B : ∀ n : ℕ, S n ≫ B n = 0
  B_comp_I : ∀ n : ℕ, B n ≫ I (n + 1) = 0
  I_comp_S : ∀ n : ℕ, I (n + 2) ≫ S n = 0

attribute [reassoc (attr := simp)] NatSBIDiagram.S_comp_B
  NatSBIDiagram.B_comp_I NatSBIDiagram.I_comp_S

namespace NatSBIDiagram

/-- A morphism of natural-number indexed SBI diagrams. -/
structure Hom (D D' : NatSBIDiagram (A := A)) where
  /-- Map on ordinary homology. -/
  hMap : ∀ n : ℕ, D.H n ⟶ D'.H n
  /-- Map on cyclic-type homology. -/
  hcMap : ∀ n : ℕ, D.HC n ⟶ D'.HC n
  I_naturality : ∀ n : ℕ,
    D.I n ≫ hcMap n = hMap n ≫ D'.I n
  S_naturality : ∀ n : ℕ,
    D.S n ≫ hcMap n = hcMap (n + 2) ≫ D'.S n
  B_naturality : ∀ n : ℕ,
    D.B n ≫ hMap (n + 1) = hcMap n ≫ D'.B n

attribute [reassoc] Hom.I_naturality Hom.S_naturality Hom.B_naturality

/-- Two SBI-diagram morphisms are equal when their two families of component
maps agree pointwise. -/
@[ext]
theorem hom_ext {D D' : NatSBIDiagram (A := A)} (F G : Hom D D')
    (hH : ∀ n : ℕ, F.hMap n = G.hMap n)
    (hHC : ∀ n : ℕ, F.hcMap n = G.hcMap n) : F = G := by
  cases F
  cases G
  congr
  · funext n
    exact hH n
  · funext n
    exact hHC n

/-- The identity morphism of an SBI diagram. -/
def Hom.id (D : NatSBIDiagram (A := A)) : Hom D D where
  hMap n := 𝟙 (D.H n)
  hcMap n := 𝟙 (D.HC n)
  I_naturality n := by simp
  S_naturality n := by simp
  B_naturality n := by simp

/-- Composition of morphisms of SBI diagrams. -/
def Hom.comp {D D' D'' : NatSBIDiagram (A := A)}
    (F : Hom D D') (G : Hom D' D'') : Hom D D'' where
  hMap n := F.hMap n ≫ G.hMap n
  hcMap n := F.hcMap n ≫ G.hcMap n
  I_naturality n := by
    rw [F.I_naturality_assoc, G.I_naturality]
    simp only [Category.assoc]
  S_naturality n := by
    rw [F.S_naturality_assoc, G.S_naturality]
    simp only [Category.assoc]
  B_naturality n := by
    rw [F.B_naturality_assoc, G.B_naturality]
    simp only [Category.assoc]

instance : Category.{w} (NatSBIDiagram (A := A)) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := by
    apply hom_ext <;> intro n <;> simp [Hom.id, Hom.comp]
  comp_id F := by
    apply hom_ext <;> intro n <;> simp [Hom.id, Hom.comp]
  assoc F G H := by
    apply hom_ext <;> intro n <;> simp [Hom.comp, Category.assoc]

@[simp]
theorem id_hMap (D : NatSBIDiagram (A := A)) (n : ℕ) :
    (𝟙 D : D ⟶ D).hMap n = 𝟙 (D.H n) :=
  rfl

@[simp]
theorem id_hcMap (D : NatSBIDiagram (A := A)) (n : ℕ) :
    (𝟙 D : D ⟶ D).hcMap n = 𝟙 (D.HC n) :=
  rfl

@[simp]
theorem comp_hMap {D D' D'' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (G : D' ⟶ D'') (n : ℕ) :
    (F ≫ G).hMap n = F.hMap n ≫ G.hMap n :=
  rfl

@[simp]
theorem comp_hcMap {D D' D'' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (G : D' ⟶ D'') (n : ℕ) :
    (F ≫ G).hcMap n = F.hcMap n ≫ G.hcMap n :=
  rfl

/-- Evaluation of an SBI diagram on ordinary homology in degree `n`. -/
@[simps, implicit_reducible]
def evalH (n : ℕ) : NatSBIDiagram (A := A) ⥤ A where
  obj D := D.H n
  map F := F.hMap n

/-- Evaluation of an SBI diagram on cyclic-type homology in degree `n`. -/
@[simps, implicit_reducible]
def evalHC (n : ℕ) : NatSBIDiagram (A := A) ⥤ A where
  obj D := D.HC n
  map F := F.hcMap n

/-- Construct an isomorphism of SBI diagrams from pointwise isomorphisms
which commute with `I`, `S`, and `B`. -/
@[simps, implicit_reducible]
def Hom.isoOfComponents {D D' : NatSBIDiagram (A := A)}
    (eH : ∀ n : ℕ, D.H n ≅ D'.H n)
    (eHC : ∀ n : ℕ, D.HC n ≅ D'.HC n)
    (hI : ∀ n : ℕ,
      D.I n ≫ (eHC n).hom = (eH n).hom ≫ D'.I n)
    (hS : ∀ n : ℕ,
      D.S n ≫ (eHC n).hom = (eHC (n + 2)).hom ≫ D'.S n)
    (hB : ∀ n : ℕ,
      D.B n ≫ (eH (n + 1)).hom = (eHC n).hom ≫ D'.B n) :
    D ≅ D' where
  hom :=
    { hMap := fun n => (eH n).hom
      hcMap := fun n => (eHC n).hom
      I_naturality := hI
      S_naturality := hS
      B_naturality := hB }
  inv :=
    { hMap := fun n => (eH n).inv
      hcMap := fun n => (eHC n).inv
      I_naturality := fun n => by
        apply (cancel_mono (eHC n).hom).1
        simp only [Category.assoc, hI, Iso.inv_hom_id,
          Iso.inv_hom_id_assoc, Category.comp_id]
      S_naturality := fun n => by
        apply (cancel_mono (eHC n).hom).1
        simp only [Category.assoc, hS, Iso.inv_hom_id,
          Iso.inv_hom_id_assoc, Category.comp_id]
      B_naturality := fun n => by
        apply (cancel_mono (eH (n + 1)).hom).1
        simp only [Category.assoc, hB, Iso.inv_hom_id,
          Iso.inv_hom_id_assoc, Category.comp_id] }
  hom_inv_id := by
    apply hom_ext <;> intro n <;> simp
  inv_hom_id := by
    apply hom_ext <;> intro n <;> simp

/-- A morphism of SBI diagrams is an isomorphism when both families of
component maps consist of isomorphisms. -/
theorem Hom.isIso_of_components {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') [∀ n : ℕ, IsIso (F.hMap n)]
    [∀ n : ℕ, IsIso (F.hcMap n)] : IsIso F :=
  (Hom.isoOfComponents (fun n => asIso (F.hMap n))
    (fun n => asIso (F.hcMap n)) F.I_naturality
    F.S_naturality F.B_naturality).isIso_hom

/-- Exactness of all three consecutive pairs in an SBI diagram. -/
structure Exact (D : NatSBIDiagram (A := A)) : Prop where
  exact_SB : ∀ n : ℕ,
    (ShortComplex.mk (D.S n) (D.B n) (D.S_comp_B n)).Exact
  exact_BI : ∀ n : ℕ,
    (ShortComplex.mk (D.B n) (D.I (n + 1)) (D.B_comp_I n)).Exact
  exact_IS : ∀ n : ℕ,
    (ShortComplex.mk (D.I (n + 2)) (D.S n) (D.I_comp_S n)).Exact

/-- The two boundary properties of a connective SBI diagram. -/
structure ConnectiveBoundary (D : NatSBIDiagram (A := A)) : Prop where
  [isIso_I_zero : IsIso (D.I 0)]
  [epi_I_one : Epi (D.I 1)]

/-- Minimal degree-zero comparison: the cyclic degree-zero map is an
isomorphism when both degree-zero inclusions and the ordinary degree-zero map
are isomorphisms. -/
theorem Hom.isIso_hcMap_zero_of_isIso_I
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    [IsIso (D.I 0)] [IsIso (D'.I 0)] [IsIso (F.hMap 0)] :
    IsIso (F.hcMap 0) := by
  have : IsIso (D.I 0 ≫ F.hcMap 0) := by
    rw [F.I_naturality 0]
    infer_instance
  exact IsIso.of_isIso_comp_left (D.I 0) (F.hcMap 0)

/-- Degree-zero comparison using bundled connective boundary conditions. -/
theorem Hom.isIso_hcMap_zero {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    [IsIso (F.hMap 0)] : IsIso (F.hcMap 0) := by
  let _ : IsIso (D.I 0) := cD.isIso_I_zero
  let _ : IsIso (D'.I 0) := cD'.isIso_I_zero
  exact F.isIso_hcMap_zero_of_isIso_I

end NatSBIDiagram

end ZeroMorphisms

namespace NatSBIDiagram

section Abelian

variable {A : Type u} [Category.{w} A] [Abelian A]

private noncomputable abbrev window (D : NatSBIDiagram (A := A))
    (n : ℕ) : ComposableArrows A 4 :=
  mk₄ (D.B (n + 1)) (D.I (n + 2)) (D.S n) (D.B n)

private theorem window_exact (D : NatSBIDiagram (A := A))
    (hD : D.Exact) (n : ℕ) : (D.window n).Exact :=
  exact_of_δ₀ (hD.exact_BI (n + 1)).exact_toComposableArrows
    (exact_of_δ₀ (hD.exact_IS n).exact_toComposableArrows
      (hD.exact_SB n).exact_toComposableArrows)

private noncomputable def Hom.windowMap
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D') (n : ℕ) :
    D.window n ⟶ D'.window n :=
  homMk₄ (F.hcMap (n + 1)) (F.hMap (n + 2)) (F.hcMap (n + 2))
    (F.hcMap n) (F.hMap (n + 1))
    (F.B_naturality (n + 1)) (F.I_naturality (n + 2))
    (F.S_naturality n) (F.B_naturality n)

/-- Minimal degree-one comparison, stated using only the two exact short
complexes and the four map properties used by the diagram lemma. -/
theorem Hom.isIso_hcMap_one_of_exact {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D')
    (hD : (ShortComplex.mk (D.B 0) (D.I 1) (D.B_comp_I 0)).Exact)
    (hD' : (ShortComplex.mk (D'.B 0) (D'.I 1) (D'.B_comp_I 0)).Exact)
    [Epi (D.I 1)] [Epi (D'.I 1)]
    [IsIso (F.hMap 1)] [Epi (F.hcMap 0)] : IsIso (F.hcMap 1) := by
  let R := (mk₂ (D.B 0) (D.I 1) : ComposableArrows A 2)
  let R' := (mk₂ (D'.B 0) (D'.I 1) : ComposableArrows A 2)
  let φ : R ⟶ R' := homMk₂ (F.hcMap 0) (F.hMap 1) (F.hcMap 1)
    (F.B_naturality 0) (F.I_naturality 1)
  have hR : R.Exact := hD.exact_toComposableArrows
  have hR' : R'.Exact := hD'.exact_toComposableArrows
  have happ₀ : app' φ 0 = F.hcMap 0 := by
    dsimp only [φ]
    exact homMk₂_app_zero _ _ _ _ _
  have happ₁ : app' φ 1 = F.hMap 1 := by
    dsimp only [φ]
    exact homMk₂_app_one _ _ _ _ _
  have hφ₀ : Epi (app' φ 0) := by
    rw [happ₀]
    infer_instance
  have hφ₁ : IsIso (app' φ 1) := by
    rw [happ₁]
    infer_instance
  exact CategoryTheory.Abelian.isIso_of_epi_of_isIso φ hR hR'
    (inferInstance : Epi (D.I 1)) (inferInstance : Epi (D'.I 1)) hφ₀ hφ₁

/-- Degree-one comparison using exact SBI diagrams and bundled connective
boundary conditions. -/
theorem Hom.isIso_hcMap_one {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    [IsIso (F.hMap 1)] [Epi (F.hcMap 0)] : IsIso (F.hcMap 1) := by
  let _ : Epi (D.I 1) := cD.epi_I_one
  let _ : Epi (D'.I 1) := cD'.epi_I_one
  exact F.isIso_hcMap_one_of_exact (hD.exact_BI 0) (hD'.exact_BI 0)

/-- The five-lemma step from degrees `n` and `n + 1` to degree `n + 2`. -/
theorem Hom.isIso_hcMap_add_two {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (hD : D.Exact) (hD' : D'.Exact) (n : ℕ)
    [Epi (F.hcMap (n + 1))] [IsIso (F.hMap (n + 2))]
    [IsIso (F.hcMap n)] [Mono (F.hMap (n + 1))] :
    IsIso (F.hcMap (n + 2)) := by
  let φ := F.windowMap n
  have hR : (D.window n).Exact := D.window_exact hD n
  have hR' : (D'.window n).Exact := D'.window_exact hD' n
  have happ₀ : app' φ 0 = F.hcMap (n + 1) := by
    dsimp only [φ, Hom.windowMap]
    exact homMk₄_app_zero _ _ _ _ _ _ _ _ _
  have happ₁ : app' φ 1 = F.hMap (n + 2) := by
    dsimp only [φ, Hom.windowMap]
    exact homMk₄_app_one _ _ _ _ _ _ _ _ _
  have happ₃ : app' φ 3 = F.hcMap n := by
    dsimp only [φ, Hom.windowMap]
    exact homMk₄_app_three _ _ _ _ _ _ _ _ _
  have happ₄ : app' φ 4 = F.hMap (n + 1) := by
    dsimp only [φ, Hom.windowMap]
    exact homMk₄_app_four _ _ _ _ _ _ _ _ _
  have hφ₀ : Epi (app' φ 0) := by
    rw [happ₀]
    infer_instance
  have hφ₁ : IsIso (app' φ 1) := by
    rw [happ₁]
    infer_instance
  have hφ₃ : IsIso (app' φ 3) := by
    rw [happ₃]
    infer_instance
  have hφ₄ : Mono (app' φ 4) := by
    rw [happ₄]
    infer_instance
  exact CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    hR hR' φ hφ₀ hφ₁ hφ₃ hφ₄

/-- A bounded SBI comparison theorem.  To prove the cyclic-type map in degree
`n` is an isomorphism, ordinary-homology isomorphisms are only required in
degrees at most `n`. -/
theorem Hom.isIso_hcMap_of_isIso_hMap_le
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary) (n : ℕ) :
    (∀ m : ℕ, m ≤ n → IsIso (F.hMap m)) → IsIso (F.hcMap n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      intro h
      rcases n with _ | n
      · let _ : IsIso (F.hMap 0) := h 0 le_rfl
        exact F.isIso_hcMap_zero cD cD'
      · rcases n with _ | n
        · let _ : IsIso (F.hMap 0) := h 0 (by omega)
          let _ : IsIso (F.hMap 1) := h 1 le_rfl
          let _ : IsIso (F.hcMap 0) :=
            F.isIso_hcMap_zero cD cD'
          exact F.isIso_hcMap_one hD hD' cD cD'
        · let _ : IsIso (F.hcMap n) :=
            ih n (by omega) (fun m hm => h m (by omega))
          let _ : IsIso (F.hcMap (n + 1)) :=
            ih (n + 1) (by omega) (fun m hm => h m (by omega))
          let _ : IsIso (F.hMap (n + 1)) := h (n + 1) (by omega)
          let _ : IsIso (F.hMap (n + 2)) := h (n + 2) le_rfl
          exact F.isIso_hcMap_add_two hD hD' n

/-- An isomorphism on ordinary homology in every degree induces an
isomorphism on cyclic-type homology in every degree. -/
theorem Hom.isIso_hcMap_of_isIso_hMap
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    (h : ∀ n : ℕ, IsIso (F.hMap n)) (n : ℕ) : IsIso (F.hcMap n) :=
  F.isIso_hcMap_of_isIso_hMap_le hD hD' cD cD' n (fun m _ => h m)

end Abelian

end NatSBIDiagram

end CategoryTheory

namespace CategoryTheory.NatSBIDiagram

open Limits

section ReverseZero

variable {A : Type u} [Category.{w} A] [HasZeroMorphisms A]

/-- Degree-zero ordinary homology is determined by the invertible I maps and HC map. -/
theorem Hom.isIso_hMap_zero_of_isIso_I
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    [IsIso (D.I 0)] [IsIso (D'.I 0)] [IsIso (F.hcMap 0)] :
    IsIso (F.hMap 0) := by
  let : IsIso (F.hMap 0 ≫ D'.I 0) := by
    rw [← F.I_naturality 0]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.hMap 0) (D'.I 0)

/-- The connective degree-zero boundary gives the same actual reverse comparison. -/
theorem Hom.isIso_hMap_zero {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    [IsIso (F.hcMap 0)] : IsIso (F.hMap 0) := by
  let : IsIso (D.I 0) := cD.isIso_I_zero
  let : IsIso (D'.I 0) := cD'.isIso_I_zero
  exact F.isIso_hMap_zero_of_isIso_I

end ReverseZero

section ReverseAbelian

variable {A : Type u} [Category.{w} A] [Abelian A]

open scoped ZeroObject

/-- The degree-one reverse comparison uses only the two exact pairs and I₁ epis. -/
theorem Hom.isIso_hMap_one_of_exact {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D')
    (hSB : (ShortComplex.mk (D.S 0) (D.B 0) (D.S_comp_B 0)).Exact)
    (hSB' : (ShortComplex.mk (D'.S 0) (D'.B 0) (D'.S_comp_B 0)).Exact)
    (hBI : (ShortComplex.mk (D.B 0) (D.I 1) (D.B_comp_I 0)).Exact)
    (hBI' : (ShortComplex.mk (D'.B 0) (D'.I 1) (D'.B_comp_I 0)).Exact)
    [Epi (D.I 1)] [Epi (D'.I 1)]
    [Epi (F.hcMap 2)] [IsIso (F.hcMap 0)] [IsIso (F.hcMap 1)] :
    IsIso (F.hMap 1) := by
  let R : ComposableArrows A 4 :=
    mk₄ (D.S 0) (D.B 0) (D.I 1) (0 : D.HC 1 ⟶ (0 : A))
  let R' : ComposableArrows A 4 :=
    mk₄ (D'.S 0) (D'.B 0) (D'.I 1) (0 : D'.HC 1 ⟶ (0 : A))
  let φ : R ⟶ R' :=
    homMk₄ (F.hcMap 2) (F.hcMap 0) (F.hMap 1) (F.hcMap 1) (𝟙 (0 : A))
      (F.S_naturality 0) (F.B_naturality 0) (F.I_naturality 1) (by
        change (0 : D.HC 1 ⟶ (0 : A)) ≫ 𝟙 (0 : A) =
          F.hcMap 1 ≫ (0 : D'.HC 1 ⟶ (0 : A))
        simp only [zero_comp, comp_zero])
  have hLast : (ShortComplex.mk (D.I 1) (0 : D.HC 1 ⟶ (0 : A)) (by simp)).Exact := by
    rw [ShortComplex.exact_iff_epi _ (by simp)]
    infer_instance
  have hLast' : (ShortComplex.mk (D'.I 1) (0 : D'.HC 1 ⟶ (0 : A)) (by simp)).Exact := by
    rw [ShortComplex.exact_iff_epi _ (by simp)]
    infer_instance
  have hR : R.Exact := exact_of_δ₀ hSB.exact_toComposableArrows
    (exact_of_δ₀ hBI.exact_toComposableArrows hLast.exact_toComposableArrows)
  have hR' : R'.Exact := exact_of_δ₀ hSB'.exact_toComposableArrows
    (exact_of_δ₀ hBI'.exact_toComposableArrows hLast'.exact_toComposableArrows)
  have happ₀ : app' φ 0 = F.hcMap 2 := by
    dsimp only [φ]
    exact homMk₄_app_zero _ _ _ _ _ _ _ _ _
  have happ₁ : app' φ 1 = F.hcMap 0 := by
    dsimp only [φ]
    exact homMk₄_app_one _ _ _ _ _ _ _ _ _
  have happ₂ : app' φ 2 = F.hMap 1 := by
    dsimp only [φ]
    exact homMk₄_app_two _ _ _ _ _ _ _ _ _
  have happ₃ : app' φ 3 = F.hcMap 1 := by
    dsimp only [φ]
    exact homMk₄_app_three _ _ _ _ _ _ _ _ _
  have happ₄ : app' φ 4 = 𝟙 (0 : A) := by
    dsimp only [φ]
    exact homMk₄_app_four _ _ _ _ _ _ _ _ _
  have hφ₀ : Epi (app' φ 0) := by rw [happ₀]; infer_instance
  have hφ₁ : IsIso (app' φ 1) := by rw [happ₁]; infer_instance
  have hφ₃ : IsIso (app' φ 3) := by rw [happ₃]; infer_instance
  have hφ₄ : Mono (app' φ 4) := by rw [happ₄]; infer_instance
  have h := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    hR hR' φ hφ₀ hφ₁ hφ₃ hφ₄
  rwa [happ₂] at h

/-- Exactness and the connective boundary supply the degree-one reverse comparison. -/
theorem Hom.isIso_hMap_one {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    [Epi (F.hcMap 2)] [IsIso (F.hcMap 0)] [IsIso (F.hcMap 1)] :
    IsIso (F.hMap 1) := by
  let : Epi (D.I 1) := cD.epi_I_one
  let : Epi (D'.I 1) := cD'.epi_I_one
  exact F.isIso_hMap_one_of_exact (hD.exact_SB 0) (hD'.exact_SB 0)
    (hD.exact_BI 0) (hD'.exact_BI 0)

private noncomputable abbrev reverseWindow (D : NatSBIDiagram (A := A))
    (n : ℕ) : ComposableArrows A 4 :=
  mk₄ (D.S (n + 1)) (D.B (n + 1)) (D.I (n + 2)) (D.S n)

private theorem reverseWindow_exact (D : NatSBIDiagram (A := A))
    (hD : D.Exact) (n : ℕ) : (D.reverseWindow n).Exact :=
  exact_of_δ₀ (hD.exact_SB (n + 1)).exact_toComposableArrows
    (exact_of_δ₀ (hD.exact_BI (n + 1)).exact_toComposableArrows
      (hD.exact_IS n).exact_toComposableArrows)

private noncomputable def Hom.reverseWindowMap
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D') (n : ℕ) :
    D.reverseWindow n ⟶ D'.reverseWindow n :=
  homMk₄ (F.hcMap (n + 3)) (F.hcMap (n + 1)) (F.hMap (n + 2))
    (F.hcMap (n + 2)) (F.hcMap n)
    (F.S_naturality (n + 1)) (F.B_naturality (n + 1))
    (F.I_naturality (n + 2)) (F.S_naturality n)

/-- The reverse five-term window determines H_(n+2) from its four HC neighbors. -/
theorem Hom.isIso_hMap_add_two {D D' : NatSBIDiagram (A := A)}
    (F : D ⟶ D') (hD : D.Exact) (hD' : D'.Exact) (n : ℕ)
    [Epi (F.hcMap (n + 3))] [IsIso (F.hcMap (n + 1))]
    [IsIso (F.hcMap (n + 2))] [Mono (F.hcMap n)] :
    IsIso (F.hMap (n + 2)) := by
  let φ := F.reverseWindowMap n
  have hR : (D.reverseWindow n).Exact := D.reverseWindow_exact hD n
  have hR' : (D'.reverseWindow n).Exact := D'.reverseWindow_exact hD' n
  have happ₀ : app' φ 0 = F.hcMap (n + 3) := by
    dsimp only [φ, Hom.reverseWindowMap]
    exact homMk₄_app_zero _ _ _ _ _ _ _ _ _
  have happ₁ : app' φ 1 = F.hcMap (n + 1) := by
    dsimp only [φ, Hom.reverseWindowMap]
    exact homMk₄_app_one _ _ _ _ _ _ _ _ _
  have happ₂ : app' φ 2 = F.hMap (n + 2) := by
    dsimp only [φ, Hom.reverseWindowMap]
    exact homMk₄_app_two _ _ _ _ _ _ _ _ _
  have happ₃ : app' φ 3 = F.hcMap (n + 2) := by
    dsimp only [φ, Hom.reverseWindowMap]
    exact homMk₄_app_three _ _ _ _ _ _ _ _ _
  have happ₄ : app' φ 4 = F.hcMap n := by
    dsimp only [φ, Hom.reverseWindowMap]
    exact homMk₄_app_four _ _ _ _ _ _ _ _ _
  have hφ₀ : Epi (app' φ 0) := by rw [happ₀]; infer_instance
  have hφ₁ : IsIso (app' φ 1) := by rw [happ₁]; infer_instance
  have hφ₃ : IsIso (app' φ 3) := by rw [happ₃]; infer_instance
  have hφ₄ : Mono (app' φ 4) := by rw [happ₄]; infer_instance
  have h := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    hR hR' φ hφ₀ hφ₁ hφ₃ hφ₄
  rwa [happ₂] at h

/-- A bounded reverse SBI comparison requires HC isomorphisms only through degree n+1. -/
theorem Hom.isIso_hMap_of_isIso_hcMap_le
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary) (n : ℕ)
    (h : ∀ m : ℕ, m ≤ n + 1 → IsIso (F.hcMap m)) : IsIso (F.hMap n) := by
  rcases n with _ | n
  · let : IsIso (F.hcMap 0) := h 0 (by omega)
    exact F.isIso_hMap_zero cD cD'
  · rcases n with _ | n
    · let : IsIso (F.hcMap 0) := h 0 (by omega)
      let : IsIso (F.hcMap 1) := h 1 (by omega)
      let : IsIso (F.hcMap 2) := h 2 le_rfl
      exact F.isIso_hMap_one hD hD' cD cD'
    · let : IsIso (F.hcMap n) := h n (by omega)
      let : IsIso (F.hcMap (n + 1)) := h (n + 1) (by omega)
      let : IsIso (F.hcMap (n + 2)) := h (n + 2) (by omega)
      let : IsIso (F.hcMap (n + 3)) := h (n + 3) le_rfl
      exact F.isIso_hMap_add_two hD hD' n

/-- Isomorphisms on all actual nonnegative HC maps give isomorphisms on all ordinary maps. -/
theorem Hom.isIso_hMap_of_isIso_hcMap
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary)
    (h : ∀ n : ℕ, IsIso (F.hcMap n)) (n : ℕ) : IsIso (F.hMap n) :=
  F.isIso_hMap_of_isIso_hcMap_le hD hD' cD cD' n (fun m _ => h m)

/-- For actual exact connective SBI diagrams, the two componentwise comparisons are equivalent. -/
theorem Hom.isIso_hMap_iff_isIso_hcMap
    {D D' : NatSBIDiagram (A := A)} (F : D ⟶ D')
    (hD : D.Exact) (hD' : D'.Exact)
    (cD : D.ConnectiveBoundary) (cD' : D'.ConnectiveBoundary) :
    (∀ n : ℕ, IsIso (F.hMap n)) ↔ ∀ n : ℕ, IsIso (F.hcMap n) :=
  ⟨fun h n => F.isIso_hcMap_of_isIso_hMap hD hD' cD cD' h n,
    fun h n => F.isIso_hMap_of_isIso_hcMap hD hD' cD cD' h n⟩

end ReverseAbelian

end CategoryTheory.NatSBIDiagram
