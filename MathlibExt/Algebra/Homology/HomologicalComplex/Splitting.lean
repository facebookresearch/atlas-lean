/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Splittings for arbitrary homological complex shapes

A splitting is a degree-one family h with d h d = d. The extra components
outside the reversed complex shape are zero. This uses a category with zero
morphisms; it makes no assumption about rings, module categories, projectives,
or a relation between object, morphism and index universes.

The preadditive layer normalizes a splitting to satisfy h d h = h and h² = 0.
These additional laws are proved for the normalization, not assumed of an
arbitrary splitting family. The literal chain and cochain formulas are recovered
by the complex-shape relation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- Degree-one generalized inverses of the actual differentials. -/
structure Splitting (K : HomologicalComplex C c) where
  /-- The backward-degree components, in the same direction as Homotopy.hom. -/
  hom : ∀ i j : ι, K.X i ⟶ K.X j
  /-- Components away from the reverse differential relation vanish. -/
  zero : ∀ i j : ι, ¬c.Rel j i → hom i j = 0
  /-- Each differential is fixed by inserting its generalized inverse. -/
  d_h_d : ∀ i j : ι, K.d i j ≫ hom j i ≫ K.d i j = K.d i j

/-- A homological complex is split when it admits degree-one generalized inverses. -/
def IsSplit (K : HomologicalComplex C c) : Prop :=
  Nonempty (Splitting K)

namespace Splitting

variable {K L M : HomologicalComplex C c}

/-- Splitting data agree when every degree-one component agrees. -/
@[ext]
lemma ext {s t : Splitting K} (h : ∀ i j, s.hom i j = t.hom i j) : s = t := by
  cases s
  cases t
  congr
  funext i j
  exact h i j

/-- Zero differentials have the zero splitting, without additive hypotheses. -/
def ofZero (h : ∀ i j, K.d i j = 0) : Splitting K where
  hom _ _ := 0
  zero _ _ _ := rfl
  d_h_d i j := by simp only [h i j, comp_zero]

/-- The zero splitting has zero components. -/
@[simp]
lemma ofZero_hom (h : ∀ i j, K.d i j = 0) (i j : ι) :
    (ofZero h).hom i j = 0 := rfl

/-- The differential followed by its generalized inverse is idempotent. -/
lemma d_hom_idempotent (s : Splitting K) (i j : ι) :
    (K.d i j ≫ s.hom j i) ≫ (K.d i j ≫ s.hom j i) =
      K.d i j ≫ s.hom j i := by
  calc
    _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i := by
      simp only [Category.assoc]
    _ = K.d i j ≫ s.hom j i := by rw [s.d_h_d i j]

/-- The generalized inverse followed by its differential is idempotent. -/
lemma hom_d_idempotent (s : Splitting K) (i j : ι) :
    (s.hom i j ≫ K.d j i) ≫ (s.hom i j ≫ K.d j i) =
      s.hom i j ≫ K.d j i := by
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i := by rw [s.d_h_d j i]

/-- Inserting the differential once normalizes every inverse reflexively. -/
def reflexive (s : Splitting K) : Splitting K where
  hom i j := s.hom i j ≫ K.d j i ≫ s.hom i j
  zero i j hij := by simp only [s.zero i j hij, comp_zero]
  d_h_d i j := by
    calc
      _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i ≫ K.d i j := by
        simp only [Category.assoc]
      _ = K.d i j ≫ s.hom j i ≫ K.d i j :=
        congrArg (fun a : K.X i ⟶ K.X j => a ≫ s.hom j i ≫ K.d i j) (s.d_h_d i j)
      _ = K.d i j := s.d_h_d i j

/-- The reflexive normalization has the explicit h d h components. -/
lemma reflexive_hom (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j = s.hom i j ≫ K.d j i ≫ s.hom i j := rfl

/-- The reflexive normalization satisfies h d h = h. -/
lemma reflexive_h_d_h (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j = s.reflexive.hom i j := by
  dsimp only [reflexive]
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) ≫
        s.hom i j ≫ K.d j i ≫ s.hom i j := by simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i ≫ s.hom i j ≫ K.d j i ≫ s.hom i j := by
      rw [s.d_h_d j i]
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) ≫ s.hom i j := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i ≫ s.hom i j := by rw [s.d_h_d j i]

/-- Reflexive normalization preserves the differential-first projection. -/
lemma d_reflexive_hom (s : Splitting K) (i j : ι) :
    K.d i j ≫ s.reflexive.hom j i = K.d i j ≫ s.hom j i := by
  change K.d i j ≫ (s.hom j i ≫ K.d i j ≫ s.hom j i) = _
  calc
    _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i := by
      simp only [Category.assoc]
    _ = K.d i j ≫ s.hom j i := by rw [s.d_h_d i j]

/-- Reflexive normalization preserves the inverse-first projection. -/
lemma reflexive_hom_d (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j ≫ K.d j i = s.hom i j ≫ K.d j i := by
  change (s.hom i j ≫ K.d j i ≫ s.hom i j) ≫ K.d j i = _
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i := by rw [s.d_h_d j i]

/-- An isomorphism transports the actual degree-one inverse components. -/
def ofIso (s : Splitting K) (e : K ≅ L) : Splitting L where
  hom i j := e.inv.f i ≫ s.hom i j ≫ e.hom.f j
  zero i j hij := by simp only [s.zero i j hij, comp_zero, zero_comp]
  d_h_d i j := by
    have hId : e.inv.f j ≫ e.hom.f j = 𝟙 (L.X j) := by
      have h := congrArg (fun f : L ⟶ L => f.f j) e.inv_hom_id
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using h
    calc
      _ = e.inv.f i ≫ (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ e.hom.f j := by
        simp only [Category.assoc]
        rw [← e.inv.comm_assoc i j, e.hom.comm i j]
      _ = e.inv.f i ≫ K.d i j ≫ e.hom.f j := by rw [s.d_h_d i j]
      _ = L.d i j ≫ e.inv.f j ≫ e.hom.f j := by rw [e.inv.comm_assoc i j]
      _ = L.d i j := by rw [hId, Category.comp_id]

/-- Transport keeps the explicit conjugation of each component. -/
lemma ofIso_hom (s : Splitting K) (e : K ≅ L) (i j : ι) :
    (s.ofIso e).hom i j = e.inv.f i ≫ s.hom i j ≫ e.hom.f j := rfl

/-- Identity transport fixes the splitting data. -/
@[simp]
lemma ofIso_refl (s : Splitting K) : s.ofIso (Iso.refl K) = s := by
  ext i j
  simp only [ofIso, Iso.refl_inv, Iso.refl_hom, HomologicalComplex.id_f,
    Category.id_comp, Category.comp_id]

/-- Consecutive transports equal transport along the composite isomorphism. -/
lemma ofIso_trans (s : Splitting K) (e : K ≅ L) (f : L ≅ M) :
    (s.ofIso e).ofIso f = s.ofIso (e ≪≫ f) := by
  ext i j
  simp only [ofIso, Iso.trans_inv, Iso.trans_hom, HomologicalComplex.comp_f, Category.assoc]

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/-- A zero-preserving functor transports every actual inverse component. -/
def map (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    Splitting ((F.mapHomologicalComplex c).obj K) where
  hom i j := F.map (s.hom i j)
  zero i j hij := by rw [s.zero i j hij, F.map_zero]
  d_h_d i j := by
    change F.map (K.d i j) ≫ F.map (s.hom j i) ≫ F.map (K.d i j) = F.map (K.d i j)
    rw [← F.map_comp, ← F.map_comp, s.d_h_d i j]

/-- The functor transport has the literal mapped components. -/
lemma map_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i j : ι) :
    (s.map F).hom i j = F.map (s.hom i j) := rfl

end Splitting

/-- Zero differentials imply the split predicate in every complex shape. -/
lemma isSplit_of_d_eq_zero {K : HomologicalComplex C c} (h : ∀ i j, K.d i j = 0) :
    IsSplit K :=
  ⟨Splitting.ofZero h⟩

/-- The split predicate is invariant under a genuine complex isomorphism. -/
lemma isSplit_iff_of_iso {K L : HomologicalComplex C c} (e : K ≅ L) :
    IsSplit K ↔ IsSplit L := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.ofIso e⟩
  · rintro ⟨s⟩
    exact ⟨s.ofIso e.symm⟩

/-- Any zero-preserving functor sends split complexes to split complexes. -/
lemma IsSplit.map {K : HomologicalComplex C c} (h : IsSplit K)
    {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    IsSplit ((F.mapHomologicalComplex c).obj K) := by
  obtain ⟨s⟩ := h
  exact ⟨s.map F⟩

end ZeroMorphisms

section Preadditive

variable [Preadditive C]

namespace Splitting

variable {K : HomologicalComplex C c}

/-- Normalize inverse maps so consecutive degree-one components vanish. -/
noncomputable def normalize (s : Splitting K) : Splitting K where
  hom i j :=
    (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
      s.reflexive.hom i j
  zero i j hij := by
    rw [s.reflexive.zero i j hij, comp_zero]
  d_h_d i j := by
    have h : K.d i j ≫
        (𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j) = K.d i j := by
      simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        K.d_comp_d, zero_comp, sub_zero]
    calc
      _ = (K.d i j ≫
          (𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j)) ≫
            s.reflexive.hom j i ≫ K.d i j := by simp only [Category.assoc]
      _ = K.d i j ≫ s.reflexive.hom j i ≫ K.d i j := by rw [h]
      _ = K.d i j := s.reflexive.d_h_d i j

/-- The normalized components have the explicit source-projection formula. -/
lemma normalize_hom (s : Splitting K) (i j : ι) :
    s.normalize.hom i j =
      (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
        s.reflexive.hom i j := rfl

/-- Normalization satisfies the reflexive generalized-inverse law. -/
lemma normalize_h_d_h (s : Splitting K) (i j : ι) :
    s.normalize.hom i j ≫ K.d j i ≫ s.normalize.hom i j = s.normalize.hom i j := by
  let a : K.X i ⟶ K.X i :=
    𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i
  have hd : K.d j i ≫ a = K.d j i := by
    dsimp only [a]
    simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      K.d_comp_d, zero_comp, sub_zero]
  change (a ≫ s.reflexive.hom i j) ≫ K.d j i ≫
      (a ≫ s.reflexive.hom i j) = a ≫ s.reflexive.hom i j
  calc
    _ = a ≫ s.reflexive.hom i j ≫ (K.d j i ≫ a) ≫ s.reflexive.hom i j := by
      simp only [Category.assoc]
    _ = a ≫ s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j := by rw [hd]
    _ = a ≫ (s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j) := rfl
    _ = a ≫ s.reflexive.hom i j := by rw [s.reflexive_h_d_h i j]

/-- Every consecutive pair of normalized inverse components has zero composite. -/
lemma normalize_hom_comp_hom (s : Splitting K) (i j k : ι) :
    s.normalize.hom i j ≫ s.normalize.hom j k = 0 := by
  by_cases hij : c.Rel j i
  · have hnext : c.next j = i := c.next_eq' hij
    have hzero : s.reflexive.hom i j ≫
        (𝟙 (K.X j) - K.d j i ≫ s.reflexive.hom i j) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id]
      rw [s.reflexive_h_d_h i j, sub_self]
    change
      ((𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
        s.reflexive.hom i j) ≫
      ((𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j) ≫
        s.reflexive.hom j k) = 0
    rw [hnext]
    calc
      _ = (𝟙 (K.X i) - K.d i (c.next i) ≫
          s.reflexive.hom (c.next i) i) ≫
            (s.reflexive.hom i j ≫
              (𝟙 (K.X j) - K.d j i ≫ s.reflexive.hom i j)) ≫
                s.reflexive.hom j k := by simp only [Category.assoc]
      _ = 0 := by
        rw [hzero]
        simp only [zero_comp, comp_zero]
  · rw [s.normalize.zero i j hij, zero_comp]

end Splitting

end Preadditive

end HomologicalComplex


namespace ChainComplex

section IntegerSplittingFamily

universe uChain vChain

variable {C : Type uChain} [Category.{vChain} C] [HasZeroMorphisms C]

/-- An integer degree-one family with d = d s d defines the actual generic splitting. -/
def splittingOfDegreeOneHom (K : ChainComplex C ℤ)
    (s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1))
    (hs : ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n) :
    HomologicalComplex.Splitting K where
  hom i j := if h : i + 1 = j then s i ≫ eqToHom (congrArg K.X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  d_h_d i j := by
    by_cases h : j + 1 = i
    · subst i
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
      exact (hs j).symm
    · have hd : K.d i j = 0 := K.shape i j h
      simp only [hd, comp_zero]

/-- Its adjacent component is the original degree-one map. -/
lemma splittingOfDegreeOneHom_hom_succ (K : ChainComplex C ℤ)
    (s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1))
    (hs : ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n)
    (n : ℤ) :
    (splittingOfDegreeOneHom K s hs).hom n (n + 1) = s n := by
  change (if h : n + 1 = n + 1 then s n ≫ eqToHom (congrArg K.X h) else 0) = s n
  simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/-- For integer chains, the generic split predicate is the literal d = d s d condition. -/
theorem isSplit_iff_exists_degreeOneHom (K : ChainComplex C ℤ) :
    HomologicalComplex.IsSplit K ↔
      ∃ s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1),
        ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n := by
  constructor
  · rintro ⟨s⟩
    exact ⟨fun n => s.hom n (n + 1), fun n => (s.d_h_d (n + 1) n).symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨splittingOfDegreeOneHom K s hs⟩

end IntegerSplittingFamily

end ChainComplex

namespace HomologicalComplex

universe uEdge vEdge wEdge

variable {C : Type uEdge} [Category.{vEdge} C] [HasZeroMorphisms C]
  {ι : Type wEdge} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Edgewise generalized inverses give the actual shape-supported splitting.
The inverse on each allowed edge is chosen, and every other component is zero. -/
noncomputable def Splitting.ofEdgewise
    (h : ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j) : Splitting K := by
  classical
  exact {
    hom := fun i j => if hij : c.Rel j i then Classical.choose (h j i hij) else 0
    zero := fun i j hij => by simp only [dite_eq_right hij]
    d_h_d := fun i j => by
      by_cases hij : c.Rel i j
      · simp only [dite_eq_left hij]
        exact Classical.choose_spec (h i j hij)
      · simp only [K.shape i j hij, comp_zero] }

/-- On an allowed reverse edge, the constructor uses its actual chosen inverse. -/
theorem Splitting.ofEdgewise_hom_of_rel
    (h : ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j)
    (i j : ι) (hij : c.Rel j i) :
    (Splitting.ofEdgewise h).hom i j = Classical.choose (h j i hij) := by
  classical
  change (if hji : c.Rel j i then Classical.choose (h j i hji) else 0) = _
  rw [dite_eq_left hij]

/-- Arbitrary-shape splitting is exactly existence of a generalized inverse on every edge. -/
theorem isSplit_iff_edgewise (K : HomologicalComplex C c) :
    IsSplit K ↔ ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j := by
  constructor
  · rintro ⟨s⟩ i j hij
    exact ⟨s.hom j i, s.d_h_d i j⟩
  · intro h
    exact ⟨Splitting.ofEdgewise h⟩

end HomologicalComplex
