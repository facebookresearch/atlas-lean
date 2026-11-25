/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.SplittingPrismDegeneracyDescent
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Whole-source prism faces from actual nondegenerate prescriptions

A proper epi summand factors through an elementary degeneracy. Native
splitting extensionality therefore reduces each whole-source equation to
the new summand and the images of the elementary degeneracies. The latter
equations follow from the unconditional all-epi prism descent, the native
face-degeneracy identities, and the already established previous degree.
No global homotopy or new-degree whole-source equation is input.
Source proposals only; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] {P : SimplicialObject C} (s : Splitting P)

/-- The actual new summand and all elementary degeneracy images determine
a map from the whole next source degree. -/
theorem hom_ext_new_degenerate {n : ℕ} {Z : C} {a b : P.obj (op ⦋n + 1⦌) ⟶ Z}
    (hnew : s.ι (n + 1) ≫ a = s.ι (n + 1) ≫ b)
    (hdeg : ∀ i : Fin (n + 1), P.σ i ≫ a = P.σ i ≫ b) : a = b := by
  apply s.hom_ext'
  intro t
  by_cases ht : t.EqId
  · change t = IndexSet.id _ at ht
    subst t
    rw [s.cofan_inj_id (n + 1)]
    exact hnew
  · have hnot : ¬ Function.Injective t.e.toOrderHom := by
      intro hi
      exact ht (t.eqId_iff_mono.mpr (SimplexCategory.mono_iff_injective.mpr hi))
    obtain ⟨i, e, he⟩ := SimplexCategory.eq_σ_comp_of_not_injective t.e hnot
    simp only [cofan_inj_eq, he, op_comp, P.map_comp]
    change (s.ι t.1.unop.len ≫ P.map e.op ≫ P.σ i) ≫ a =
      (s.ι t.1.unop.len ≫ P.map e.op ≫ P.σ i) ≫ b
    simp only [Category.assoc]
    exact congrArg (fun z => s.ι t.1.unop.len ≫ P.map e.op ≫ z) (hdeg i)

end CategoryTheory.SimplicialObject.Splitting

namespace CategoryTheory.SimplicialObject.SplittingPrismFaceDescent

variable {C : Type u} [Category.{v} C] {P Q : SimplicialObject C}
  (s : Splitting P)
  (p : ∀ n : ℕ, Fin (n + 1) → (s.N n ⟶ Q.obj (op ⦋n + 1⦌)))
  (f g : P ⟶ Q)

/-- The original native face at the supplied finite ordinal index. -/
abbrev face (X : SimplicialObject C) (n j : ℕ) (hj : j ≤ n + 1) :=
  X.δ (⟨j, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 2))

/-- The original native degeneracy at the supplied finite ordinal index. -/
abbrev degeneracy (X : SimplicialObject C) (n a : ℕ) (ha : a ≤ n) :=
  X.σ (⟨a, Nat.lt_succ_iff.mpr ha⟩ : Fin (n + 1))

/-- These operators are always derived by native all-epi coproduct descent. -/
abbrev operator (n r : ℕ) (hr : r ≤ n) :
    P.obj (op ⦋n⦌) ⟶ Q.obj (op ⦋n + 1⦌) :=
  s.prismDegree p (⟨r, Nat.lt_succ_iff.mpr hr⟩ : Fin (n + 1))

@[reassoc]
private theorem degeneracy_operator_of_lt (n a : ℕ) (ha : a ≤ n)
    (r : ℕ) (hr : r ≤ n + 1) (har : a < r) :
    degeneracy P n a ha ≫ operator s p (n + 1) r hr =
      operator s p n (r - 1) (by omega) ≫ degeneracy Q (n + 1) a (by omega) := by
  have hv : (⟨r - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨r, Nat.lt_succ_iff.mpr hr⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change r - 1 + 1 = r
    omega
  have h := s.prismDegree_degeneracy_castSucc p
    (⟨a, by omega⟩ : Fin (n + 1)) (⟨r - 1, by omega⟩ : Fin (n + 1)) (by
      change a ≤ r - 1
      omega)
  rw [hv] at h
  change degeneracy P n a ha ≫ operator s p (n + 1) r hr =
    operator s p n (r - 1) (by omega) ≫ degeneracy Q (n + 1) a (by omega) at h
  exact h

@[reassoc]
private theorem degeneracy_operator_of_le (n a : ℕ) (ha : a ≤ n)
    (r : ℕ) (hr : r ≤ n + 1) (hra : r ≤ a) :
    degeneracy P n a ha ≫ operator s p (n + 1) r hr =
      operator s p n r (by omega) ≫ degeneracy Q (n + 1) (a + 1) (by omega) := by
  have h := s.prismDegree_degeneracy_succ p
    (⟨a, by omega⟩ : Fin (n + 1)) (⟨r, by omega⟩ : Fin (n + 1)) (by
      change r ≤ a
      exact hra)
  change degeneracy P n a ha ≫ operator s p (n + 1) r hr =
    operator s p n r (by omega) ≫ degeneracy Q (n + 1) (a + 1) (by omega) at h
  exact h

@[reassoc]
private theorem degeneracy_face_lt (X : SimplicialObject C) (n a j : ℕ)
    (ha : a ≤ n + 1) (hj : j < a) :
    degeneracy X (n + 1) a ha ≫ face X (n + 1) j (by omega) =
      face X n j (by omega) ≫ degeneracy X n (a - 1) (by omega) := by
  have h := X.δ_comp_σ_of_le
    (i := (⟨j, by omega⟩ : Fin (n + 2)))
    (j := (⟨a - 1, by omega⟩ : Fin (n + 1))) (by
      change j ≤ a - 1
      omega)
  have ha' : (⟨a - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨a, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change a - 1 + 1 = a
    omega
  have hj' : (⟨j, by omega⟩ : Fin (n + 2)).castSucc =
      (⟨j, by omega⟩ : Fin (n + 3)) := Fin.ext rfl
  rw [ha', hj'] at h
  exact h

@[reassoc]
private theorem degeneracy_face_gt (X : SimplicialObject C) (n a j : ℕ)
    (ha : a ≤ n + 1) (hj : a + 1 < j) (hj' : j ≤ n + 2) :
    degeneracy X (n + 1) a ha ≫ face X (n + 1) j hj' =
      face X n (j - 1) (by omega) ≫ degeneracy X n a (by omega) := by
  have h := X.δ_comp_σ_of_gt
    (i := (⟨j - 1, by omega⟩ : Fin (n + 2)))
    (j := (⟨a, by omega⟩ : Fin (n + 1))) (by
      change a < j - 1
      omega)
  have hj'' : (⟨j - 1, by omega⟩ : Fin (n + 2)).succ =
      (⟨j, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    change j - 1 + 1 = j
    omega
  have ha' : (⟨a, by omega⟩ : Fin (n + 1)).castSucc =
      (⟨a, by omega⟩ : Fin (n + 2)) := Fin.ext rfl
  rw [hj'', ha'] at h
  exact h

@[reassoc]
private theorem degeneracy_face_self (X : SimplicialObject C) (n a : ℕ) (ha : a ≤ n) :
    degeneracy X n a ha ≫ face X n a (by omega) = 𝟙 _ :=
  X.δ_comp_σ_self (i := (⟨a, by omega⟩ : Fin (n + 1)))

@[reassoc]
private theorem degeneracy_face_succ (X : SimplicialObject C) (n a : ℕ) (ha : a ≤ n) :
    degeneracy X n a ha ≫ face X n (a + 1) (by omega) = 𝟙 _ :=
  X.δ_comp_σ_succ (i := (⟨a, by omega⟩ : Fin (n + 1)))

private theorem degeneracy_naturality (q : P ⟶ Q) (n a : ℕ) (ha : a ≤ n) :
    degeneracy P n a ha ≫ q.app (op ⦋n + 1⦌) =
      q.app (op ⦋n⦌) ≫ degeneracy Q n a ha :=
  q.naturality (SimplexCategory.σ (⟨a, by omega⟩ : Fin (n + 1))).op

/-- Established whole-source faces in degree `d + 1`. -/
structure Faces (d : ℕ) : Prop where
  zero : operator s p (d + 1) 0 (by omega) ≫ face Q (d + 1) 0 (by omega) = g.app (op ⦋d + 1⦌)
  last : operator s p (d + 1) (d + 1) (by omega) ≫ face Q (d + 1) (d + 2) (by omega) =
    f.app (op ⦋d + 1⦌)
  early : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : j < r),
    operator s p (d + 1) r hr ≫ face Q (d + 1) j (by omega) =
      face P d j (by omega) ≫ operator s p d (r - 1) (by omega)
  late : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : r + 1 < j) (hj' : j ≤ d + 2),
    operator s p (d + 1) r hr ≫ face Q (d + 1) j hj' =
      face P d (j - 1) (by omega) ≫ operator s p d r (by omega)
  middle : ∀ (r : ℕ) (hr : r < d + 1),
    operator s p (d + 1) (r + 1) (by omega) ≫ face Q (d + 1) (r + 1) (by omega) =
      operator s p (d + 1) r (by omega) ≫ face Q (d + 1) (r + 1) (by omega)

/-- The new degree's equations on its actual nondegenerate summand only. -/
structure FacesOnGenerators (d : ℕ) : Prop where
  zero : s.ι (d + 1) ≫ (operator s p (d + 1) 0 (by omega) ≫ face Q (d + 1) 0 (by omega)) =
    s.ι (d + 1) ≫ g.app (op ⦋d + 1⦌)
  last : s.ι (d + 1) ≫ (operator s p (d + 1) (d + 1) (by omega) ≫
    face Q (d + 1) (d + 2) (by omega)) = s.ι (d + 1) ≫ f.app (op ⦋d + 1⦌)
  early : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : j < r),
    s.ι (d + 1) ≫ (operator s p (d + 1) r hr ≫ face Q (d + 1) j (by omega)) =
      s.ι (d + 1) ≫ (face P d j (by omega) ≫ operator s p d (r - 1) (by omega))
  late : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : r + 1 < j) (hj' : j ≤ d + 2),
    s.ι (d + 1) ≫ (operator s p (d + 1) r hr ≫ face Q (d + 1) j hj') =
      s.ι (d + 1) ≫ (face P d (j - 1) (by omega) ≫ operator s p d r (by omega))
  middle : ∀ (r : ℕ) (hr : r < d + 1),
    s.ι (d + 1) ≫ (operator s p (d + 1) (r + 1) (by omega) ≫
      face Q (d + 1) (r + 1) (by omega)) =
        s.ι (d + 1) ≫ (operator s p (d + 1) r (by omega) ≫ face Q (d + 1) (r + 1) (by omega))

variable {d : ℕ}

private theorem zero_descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1)) :
    operator s p (d + 2) 0 (by omega) ≫ face Q (d + 2) 0 (by omega) = g.app (op ⦋d + 2⦌) := by
  apply s.hom_ext_new_degenerate new.zero
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) 0 (by omega) ≫ face Q (d + 2) 0 (by omega)) = _
  rw [degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) 0 (by omega) (by omega),
    degeneracy_face_lt Q (d + 1) (a.val + 1) 0 (by omega) (by omega),
    ← Category.assoc, old.zero]
  simp only [Nat.add_sub_cancel]
  exact (degeneracy_naturality g (d + 1) a.val (by omega)).symm

private theorem last_descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1)) :
    operator s p (d + 2) (d + 2) (by omega) ≫ face Q (d + 2) (d + 3) (by omega) =
      f.app (op ⦋d + 2⦌) := by
  apply s.hom_ext_new_degenerate new.last
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) (d + 2) (by omega) ≫ face Q (d + 2) (d + 3) (by omega)) = _
  rw [degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) (d + 2) (by omega) (by omega),
    degeneracy_face_gt Q (d + 1) a.val (d + 3) (by omega) (by omega) (by omega),
    ← Category.assoc]
  have hold : operator s p (d + 1) (d + 2 - 1) (by omega) ≫
      face Q (d + 1) (d + 3 - 1) (by omega) = f.app (op ⦋d + 1⦌) := by
    have hop : operator s p (d + 1) (d + 2 - 1) (by omega) =
        operator s p (d + 1) (d + 1) (by omega) := by
      have hi : (⟨d + 2 - 1, by omega⟩ : Fin (d + 2)) =
          (⟨d + 1, by omega⟩ : Fin (d + 2)) := by
        apply Fin.ext
        change d + 2 - 1 = d + 1
        omega
      exact congrArg (s.prismDegree p) hi
    have hface : face Q (d + 1) (d + 3 - 1) (by omega) =
        face Q (d + 1) (d + 2) (by omega) := by
      have hi : (⟨d + 3 - 1, by omega⟩ : Fin (d + 3)) =
          (⟨d + 2, by omega⟩ : Fin (d + 3)) := by
        apply Fin.ext
        change d + 3 - 1 = d + 2
        omega
      exact congrArg Q.δ hi
    exact (congrArg₂ (fun x y => x ≫ y) hop hface).trans old.last
  rw [hold]
  exact (degeneracy_naturality f (d + 1) a.val (by omega)).symm

private theorem early_descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1))
    (r : ℕ) (hr : r ≤ d + 2) (j : ℕ) (hj : j < r) :
    operator s p (d + 2) r hr ≫ face Q (d + 2) j (by omega) =
      face P (d + 1) j (by omega) ≫ operator s p (d + 1) (r - 1) (by omega) := by
  apply s.hom_ext_new_degenerate (new.early r hr j hj)
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) r hr ≫ face Q (d + 2) j (by omega)) =
      degeneracy P (d + 1) a.val (by omega) ≫
        (face P (d + 1) j (by omega) ≫ operator s p (d + 1) (r - 1) (by omega))
  by_cases har : a.val < r
  · rw [degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) r hr har]
    by_cases hja : j < a.val
    · rw [degeneracy_face_lt Q (d + 1) a.val j (by omega) hja,
        ← Category.assoc, old.early (r - 1) (by omega) j (by omega),
        degeneracy_face_lt_assoc P d a.val j (by omega) hja,
        degeneracy_operator_of_lt s p d (a.val - 1) (by omega) (r - 1) (by omega) (by omega)]
      simp only [Category.assoc]
    · by_cases heq : j = a.val
      · subst j
        rw [degeneracy_face_self Q (d + 2) a.val (by omega),
          degeneracy_face_self_assoc P (d + 1) a.val (by omega)]
        simp only [Category.comp_id]
      · by_cases hsucc : j = a.val + 1
        · subst j
          rw [degeneracy_face_succ Q (d + 2) a.val (by omega),
            degeneracy_face_succ_assoc P (d + 1) a.val (by omega)]
          simp only [Category.comp_id]
        · have hgt : a.val + 1 < j := by omega
          rw [degeneracy_face_gt Q (d + 1) a.val j (by omega) hgt (by omega),
            ← Category.assoc, old.early (r - 1) (by omega) (j - 1) (by omega),
            degeneracy_face_gt_assoc P d a.val j (by omega) hgt (by omega),
            degeneracy_operator_of_lt s p d a.val (by omega) (r - 1) (by omega) (by omega)]
          simp only [Category.assoc]
  · have hra : r ≤ a.val := by omega
    rw [degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) r hr hra,
      degeneracy_face_lt Q (d + 1) (a.val + 1) j (by omega) (by omega),
      ← Category.assoc, old.early r (by omega) j hj,
      degeneracy_face_lt_assoc P d a.val j (by omega) (by omega),
      degeneracy_operator_of_le s p d (a.val - 1) (by omega) (r - 1) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.sub_add_cancel (by omega : 1 ≤ a.val), Category.assoc]

private theorem late_descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1))
    (r : ℕ) (hr : r ≤ d + 2) (j : ℕ) (hj : r + 1 < j) (hj' : j ≤ d + 3) :
    operator s p (d + 2) r hr ≫ face Q (d + 2) j hj' =
      face P (d + 1) (j - 1) (by omega) ≫ operator s p (d + 1) r (by omega) := by
  apply s.hom_ext_new_degenerate (new.late r hr j hj hj')
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) r hr ≫ face Q (d + 2) j hj') =
      degeneracy P (d + 1) a.val (by omega) ≫
        (face P (d + 1) (j - 1) (by omega) ≫ operator s p (d + 1) r (by omega))
  by_cases hra : r ≤ a.val
  · rw [degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) r hr hra]
    by_cases hja : j < a.val + 1
    · rw [degeneracy_face_lt Q (d + 1) (a.val + 1) j (by omega) hja,
        ← Category.assoc, old.late r (by omega) j hj (by omega),
        degeneracy_face_lt_assoc P d a.val (j - 1) (by omega) (by omega),
        degeneracy_operator_of_le s p d (a.val - 1) (by omega) r (by omega) (by omega)]
      simp only [Nat.add_sub_cancel, Nat.sub_add_cancel (by omega : 1 ≤ a.val), Category.assoc]
    · by_cases heq : j = a.val + 1
      · subst j
        simp only [Nat.add_sub_cancel]
        rw [degeneracy_face_self Q (d + 2) (a.val + 1) (by omega),
          degeneracy_face_self_assoc P (d + 1) a.val (by omega)]
        simp only [Category.comp_id]
      · by_cases hsucc : j = a.val + 2
        · subst j
          have hidx : a.val + 2 - 1 = a.val + 1 := by omega
          have hface : face P (d + 1) (a.val + 2 - 1) (by omega) =
              face P (d + 1) (a.val + 1) (by omega) := by
            exact congrArg P.δ (Fin.ext hidx)
          rw [hface]
          rw [degeneracy_face_succ Q (d + 2) (a.val + 1) (by omega),
            degeneracy_face_succ_assoc P (d + 1) a.val (by omega)]
          simp only [Category.comp_id]
        · have hgt : a.val + 2 < j := by omega
          rw [degeneracy_face_gt Q (d + 1) (a.val + 1) j (by omega) (by omega) hj',
            ← Category.assoc, old.late r (by omega) (j - 1) (by omega) (by omega),
            degeneracy_face_gt_assoc P d a.val (j - 1) (by omega) (by omega) (by omega),
            degeneracy_operator_of_le s p d a.val (by omega) r (by omega) hra]
          simp only [Category.assoc]
  · have har : a.val < r := by omega
    rw [degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) r hr har,
      degeneracy_face_gt Q (d + 1) a.val j (by omega) (by omega) hj',
      ← Category.assoc, old.late (r - 1) (by omega) (j - 1) (by omega) (by omega),
      degeneracy_face_gt_assoc P d a.val (j - 1) (by omega) (by omega) (by omega),
      degeneracy_operator_of_lt s p d a.val (by omega) r (by omega) har]
    simp only [Category.assoc]

private theorem middle_descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1))
    (r : ℕ) (hr : r < d + 2) :
    operator s p (d + 2) (r + 1) (by omega) ≫ face Q (d + 2) (r + 1) (by omega) =
      operator s p (d + 2) r (by omega) ≫ face Q (d + 2) (r + 1) (by omega) := by
  apply s.hom_ext_new_degenerate (new.middle r hr)
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) (r + 1) (by omega) ≫ face Q (d + 2) (r + 1) (by omega)) =
      degeneracy P (d + 1) a.val (by omega) ≫
        (operator s p (d + 2) r (by omega) ≫ face Q (d + 2) (r + 1) (by omega))
  by_cases har : a.val < r
  · rw [degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) (r + 1) (by omega) (by omega),
      degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) r (by omega) har]
    simp only [degeneracy_face_gt Q (d + 1) a.val (r + 1) (by omega) (by omega) (by omega),
      Nat.add_sub_cancel]
    have hm := old.middle (r - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r), Category.assoc] using
      congrArg (fun z => z ≫ degeneracy Q (d + 1) a.val (by omega)) hm
  · by_cases heq : a.val = r
    · have hv : a = (⟨r, by omega⟩ : Fin (d + 2)) := Fin.ext heq
      subst a
      change degeneracy P (d + 1) r (by omega) ≫
        (operator s p (d + 2) (r + 1) (by omega) ≫ face Q (d + 2) (r + 1) (by omega)) =
          degeneracy P (d + 1) r (by omega) ≫
            (operator s p (d + 2) r (by omega) ≫ face Q (d + 2) (r + 1) (by omega))
      rw [degeneracy_operator_of_lt_assoc s p (d + 1) r (by omega) (r + 1) (by omega) (by omega),
        degeneracy_operator_of_le_assoc s p (d + 1) r (by omega) r (by omega) le_rfl]
      simp only [Nat.add_sub_cancel]
      rw [degeneracy_face_succ Q (d + 2) r (by omega),
        degeneracy_face_self Q (d + 2) (r + 1) (by omega)]
    · have hra : r < a.val := by omega
      rw [degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) (r + 1) (by omega) (by omega),
        degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) r (by omega) (by omega)]
      simp only [degeneracy_face_lt Q (d + 1) (a.val + 1) (r + 1) (by omega) (by omega),
        Nat.add_sub_cancel]
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ degeneracy Q (d + 1) a.val (by omega)) (old.middle r (by omega))

/-- Every new-degree face and common middle is earned on the whole source.
The proper epi summands require only the already proved preceding faces. -/
theorem descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1)) :
    Faces s p f g (d + 1) where
  zero := zero_descend s p f g old new
  last := last_descend s p f g old new
  early := early_descend s p f g old new
  late := late_descend s p f g old new
  middle := middle_descend s p f g old new

/-- The original augmentation descends by the same new/degenerate source
extensionality. The previous augmentation is an established lower-degree
equation, and the new equation is supplied only on the actual new summand. -/
theorem augmentation_descend {A : C}
    (εP : P ⟶ (SimplicialObject.const C).obj A)
    (εQ : Q ⟶ (SimplicialObject.const C).obj A)
    (old : ∀ (r : ℕ) (hr : r ≤ d + 1), operator s p (d + 1) r hr ≫ εQ.app (op ⦋d + 2⦌) =
      εP.app (op ⦋d + 1⦌))
    (new : ∀ (r : ℕ) (hr : r ≤ d + 2),
      s.ι (d + 2) ≫ (operator s p (d + 2) r hr ≫ εQ.app (op ⦋d + 3⦌)) =
        s.ι (d + 2) ≫ εP.app (op ⦋d + 2⦌))
    (r : ℕ) (hr : r ≤ d + 2) :
    operator s p (d + 2) r hr ≫ εQ.app (op ⦋d + 3⦌) = εP.app (op ⦋d + 2⦌) := by
  apply s.hom_ext_new_degenerate (new r hr)
  intro a
  change degeneracy P (d + 1) a.val (by omega) ≫
    (operator s p (d + 2) r hr ≫ εQ.app (op ⦋d + 3⦌)) = _
  have hεQ : ∀ (b : ℕ) (hb : b ≤ d + 2),
      degeneracy Q (d + 2) b hb ≫ εQ.app (op ⦋d + 3⦌) = εQ.app (op ⦋d + 2⦌) := by
    intro b hb
    exact (εQ.naturality (SimplexCategory.σ (⟨b, by omega⟩ : Fin (d + 3))).op).trans
      (Category.comp_id _)
  have hεP : degeneracy P (d + 1) a.val (by omega) ≫ εP.app (op ⦋d + 2⦌) =
      εP.app (op ⦋d + 1⦌) :=
    (εP.naturality (SimplexCategory.σ (⟨a.val, by omega⟩ : Fin (d + 2))).op).trans
      (Category.comp_id _)
  by_cases har : a.val < r
  · rw [degeneracy_operator_of_lt_assoc s p (d + 1) a.val (by omega) r hr har,
      hεQ, old (r - 1) (by omega), hεP]
  · rw [degeneracy_operator_of_le_assoc s p (d + 1) a.val (by omega) r hr (by omega),
      hεQ, old r (by omega), hεP]

end CategoryTheory.SimplicialObject.SplittingPrismFaceDescent

end
