/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Split exact complexes and contracting homotopies

In a preadditive category, a contracting homotopy of 1_K to zero gives
splitting data and exactness wherever homology exists. Conversely, a
split acyclic complex has a normalized contracting homotopy. Thus, for
complexes with homology in every degree, split exactness is equivalent
to null-homotopy of the identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.ShortComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
Let S=(A→B→D) be a short complex in a preadditive category C, with homology. If r:B→A and
s:D→B satisfy r≫S.f+S.g≫s=1_B, then S is exact at B. Neither r nor s is assumed to split the
corresponding outer differential.
-/
lemma exact_of_middle_contraction (S : ShortComplex C) [S.HasHomology]
    (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂)
    (h : r ≫ S.f + S.g ≫ s = 𝟙 S.X₂) : S.Exact := by
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  calc
    S.iCycles ≫ S.pOpcycles = S.iCycles ≫ (𝟙 S.X₂) ≫ S.pOpcycles := by simp
    _ = S.iCycles ≫ (r ≫ S.f + S.g ≫ s) ≫ S.pOpcycles := by rw [h]
    _ = 0 := by
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        S.f_pOpcycles, S.iCycles_g_assoc, comp_zero, zero_comp, add_zero]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section Preadditive

variable [Preadditive C] {K : HomologicalComplex C c}

/--
Let K be a complex of arbitrary shape c in a preadditive category C. A homotopy H:1_K∼0
supplies splitting components H.hom i j. The homotopy identity gives dᵢⱼ≫H.hom j i≫dᵢⱼ=dᵢⱼ,
with support on reversed differential degrees.
-/
def Splitting.ofHomotopyIdZero (h : Homotopy (𝟙 K) 0) : Splitting K where
  hom := h.hom
  zero := h.zero
  d_h_d i j := by
    by_cases hij : c.Rel i j
    · have hId := h.comm j
      simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] at hId
      have hd : K.d i j ≫ dNext j h.hom = 0 := by
        change K.d i j ≫ (K.d j (c.next j) ≫ h.hom (c.next j) j) = 0
        rw [← Category.assoc, K.d_comp_d, zero_comp]
      have hp : prevD j h.hom = h.hom j i ≫ K.d i j :=
        prevD_eq h.hom hij
      have he := congrArg (fun a : K.X j ⟶ K.X j => K.d i j ≫ a) hId
      rw [Category.comp_id, Preadditive.comp_add, hd, zero_add, hp] at he
      simpa only [Category.assoc] using he.symm
    · rw [K.shape i j hij]
      simp only [comp_zero]

/--
Let K be a complex of arbitrary shape c in a preadditive category C. For a contracting
homotopy H:1_K∼0, the associated splitting has component (Splitting.ofHomotopyIdZero H).hom i
j=H.hom i j.
-/
lemma Splitting.ofHomotopyIdZero_hom (h : Homotopy (𝟙 K) 0) (i j : ι) :
    (Splitting.ofHomotopyIdZero h).hom i j = h.hom i j := rfl

end Preadditive

section ZeroMorphisms

variable [HasZeroMorphisms C]

/--
Let K be a complex of shape c in a category C with zero morphisms. It is split exact precisely
when it admits generalized-inverse splitting data and is acyclic, meaning its short complex
around every degree is exact.
-/
def IsSplitExact (K : HomologicalComplex C c) : Prop :=
  IsSplit K ∧ K.Acyclic

end ZeroMorphisms

section PreadditiveExactness

variable [Preadditive C] {K : HomologicalComplex C c}

/--
Let K be a complex of arbitrary shape c in a preadditive category C. Let s be a splitting and
assume K is acyclic. For n=s.normalize.hom,
1_{Kᵢ}=dᵢ,next(i)≫n_next(i),i+n_i,prev(i)≫d_prev(i),i at every i.
-/
lemma Splitting.normalize_sum_id (s : Splitting K) (hK : K.Acyclic) (i : ι) :
    𝟙 (K.X i) = dNext i s.normalize.hom + prevD i s.normalize.hom := by
  let a : K.X i ⟶ K.X i :=
    K.d i (c.next i) ≫ s.normalize.hom (c.next i) i
  let b : K.X i ⟶ K.X i :=
    s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i
  have haa : a ≫ a = a := s.normalize.d_hom_idempotent i (c.next i)
  have hbb : b ≫ b = b := s.normalize.hom_d_idempotent i (c.prev i)
  have hab : a ≫ b = 0 := by
    dsimp only [a, b]
    calc
      _ = K.d i (c.next i) ≫
          (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
            K.d (c.prev i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [s.normalize_hom_comp_hom (c.next i) i (c.prev i)]
        simp only [zero_comp, comp_zero]
  have hba : b ≫ a = 0 := by
    dsimp only [a, b]
    calc
      _ = s.normalize.hom i (c.prev i) ≫
          (K.d (c.prev i) i ≫ K.d i (c.next i)) ≫
            s.normalize.hom (c.next i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [K.d_comp_d]
        simp only [zero_comp, comp_zero]
  have hsum : (a + b) ≫ (a + b) = a + b := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, haa, hbb, hab, hba,
      add_zero, zero_add]
  let q : K.X i ⟶ K.X i := 𝟙 (K.X i) - (a + b)
  have hqq : q ≫ q = q :=
    CategoryTheory.Idempotents.idem_of_id_sub_idem (a + b) hsum
  have hag : a ≫ K.d i (c.next i) = K.d i (c.next i) := by
    dsimp only [a]
    rw [Category.assoc]
    exact s.normalize.d_h_d i (c.next i)
  have hbg : b ≫ K.d i (c.next i) = 0 := by
    dsimp only [b]
    rw [Category.assoc, K.d_comp_d, comp_zero]
  have hfa : K.d (c.prev i) i ≫ a = 0 := by
    dsimp only [a]
    rw [← Category.assoc, K.d_comp_d, zero_comp]
  have hfb : K.d (c.prev i) i ≫ b = K.d (c.prev i) i := by
    dsimp only [b]
    exact s.normalize.d_h_d (c.prev i) i
  have hqg : q ≫ K.d i (c.next i) = 0 := by
    dsimp only [q]
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.id_comp,
      hag, hbg, add_zero, sub_self]
  have hfq : K.d (c.prev i) i ≫ q = 0 := by
    dsimp only [q]
    simp only [Preadditive.comp_sub, Preadditive.comp_add, Category.comp_id,
      hfa, hfb, zero_add, sub_self]
  have hExact : (K.sc i).Exact := hK i
  have hqq0 : q ≫ q = 0 := hExact.comp_eq_zero
    (show q ≫ (K.sc i).g = 0 from hqg)
    (show (K.sc i).f ≫ q = 0 from hfq)
  have hq0 : q = 0 := hqq.symm.trans hqq0
  have hid : 𝟙 (K.X i) = a + b := sub_eq_zero.mp hq0
  exact hid

/--
Let K be a complex of arbitrary shape c in a preadditive category C. If s is a splitting and K
is acyclic, the normalized family n=s.normalize.hom defines a homotopy 1_K∼0, since dNext i
n+prevD i n=1_{Kᵢ} in every degree.
-/
noncomputable def Splitting.contractingHomotopy (s : Splitting K) (hK : K.Acyclic) :
    Homotopy (𝟙 K) 0 where
  hom := s.normalize.hom
  zero := s.normalize.zero
  comm i := by
    simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] using
      s.normalize_sum_id hK i

/--
Let K be a complex of arbitrary shape c in a preadditive category C. For a splitting s and an
acyclicity hypothesis on K, the contracting homotopy from 1_K to zero has component
s.normalize.hom i j at every pair i,j.
-/
lemma Splitting.contractingHomotopy_hom (s : Splitting K) (hK : K.Acyclic) (i j : ι) :
    (s.contractingHomotopy hK).hom i j = s.normalize.hom i j := rfl

/--
Let K be a complex of arbitrary shape c in a preadditive category C. Given H:1_K∼0 and
homology at degree i, the three-term complex K_prev(i)→Kᵢ→K_next(i) is exact at its middle
term.
-/
lemma exactAt_of_homotopy_id_zero (h : Homotopy (𝟙 K) 0) (i : ι) [K.HasHomology i] :
    (K.sc i).Exact := by
  apply CategoryTheory.ShortComplex.exact_of_middle_contraction (K.sc i)
    (h.hom i (c.prev i)) (h.hom (c.next i) i)
  have hi := h.comm i
  change h.hom i (c.prev i) ≫ K.d (c.prev i) i +
    K.d i (c.next i) ≫ h.hom (c.next i) i = 𝟙 (K.X i)
  simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero,
    dNext, prevD, AddMonoidHom.mk'_apply, zero_add, add_comm] using hi.symm

/--
Let K be a complex of arbitrary shape c in a preadditive category C. If homology exists at
every degree and H:1_K∼0, then K is acyclic: every homology object is zero, equivalently every
degreewise short complex is exact.
-/
lemma acyclic_of_homotopy_id_zero [∀ i, K.HasHomology i] (h : Homotopy (𝟙 K) 0) : K.Acyclic :=
  fun i => exactAt_of_homotopy_id_zero h i

/--
Let K be a complex of arbitrary shape c in a preadditive category C. Assume K has homology in
every degree. Then K is split exact if and only if there exists a homotopy from 1_K to zero.
-/
lemma isSplitExact_iff_id_nullHomotopic (K : HomologicalComplex C c)
    [∀ i, K.HasHomology i] :
    IsSplitExact K ↔ Nonempty (Homotopy (𝟙 K) 0) := by
  constructor
  · rintro ⟨⟨s⟩, hK⟩
    exact ⟨s.contractingHomotopy hK⟩
  · rintro ⟨h⟩
    exact ⟨⟨Splitting.ofHomotopyIdZero h⟩, acyclic_of_homotopy_id_zero h⟩

end PreadditiveExactness

end HomologicalComplex
