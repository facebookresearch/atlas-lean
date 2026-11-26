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
# Face identities from nondegenerate prism restrictions

Let P,Q be simplicial objects in a category C, s a splitting of P and p_{n,i} : N_n → Q_{n+1}
prescribed maps. Write H_{n,i} for their degeneracy-compatible coproduct descent. Maps out of
P_{n+1} are determined by their restriction to N_{n+1} and to each elementary degeneracy image
from P_n.

For n = d+1, Faces(d) records H_{n,0} ≫ d₀^Q = g_n, H_{n,n} ≫ d_{n+1}^Q = f_n, the early
equations H_{n,r} ≫ d_j^Q = d_j^P ≫ H_{n−1,r−1} for j < r, the late equations H_{n,r} ≫ d_j^Q
= d_{j−1}^P ≫ H_{n−1,r} for r+1 < j, and the common-middle equations H_{n,r+1} ≫ d_{r+1}^Q =
H_{n,r} ≫ d_{r+1}^Q. FacesOnGenerators(d) records the same equations after precomposition by
ι_n : N_n → P_n.

Faces(d), together with FacesOnGenerators(d+1), gives Faces(d+1). Degenerate restrictions
reduce to degree d+1 using the simplex face-degeneracy identities. The analogous argument
extends an augmentation equation from degree d+1 and its restrictions on N_{d+2} to all of
P_{d+2}. The category worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] {P : SimplicialObject C} (s : Splitting P)

/-- Extensionality on the nondegenerate summand and degeneracy images.

For a splitting s of P and maps a,b : P_{n+1} → Z, equality on ι_{n+1} : N_{n+1} → P_{n+1} and
after each σ_i : P_n → P_{n+1} implies a = b. Every proper epimorphism summand factors through
an elementary degeneracy. -/
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

/-- Face map at a bounded natural-number index.

For a simplicial object X, n : ℕ and j ≤ n+1, face X n j is d_j : X_{n+1} → X_n, indexed by
the corresponding element of Fin(n+2). -/
abbrev face (X : SimplicialObject C) (n j : ℕ) (hj : j ≤ n + 1) :=
  X.δ (⟨j, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 2))

/-- Degeneracy map at a bounded natural-number index.

For a simplicial object X, n : ℕ and a ≤ n, degeneracy X n a is σ_a : X_n → X_{n+1}, indexed
by the corresponding element of Fin(n+1). -/
abbrev degeneracy (X : SimplicialObject C) (n a : ℕ) (ha : a ≤ n) :=
  X.σ (⟨a, Nat.lt_succ_iff.mpr ha⟩ : Fin (n + 1))

/-- Prism operator at a bounded natural-number index.

For a splitting of P and a family p on its nondegenerate summands, operator n r with r ≤ n is
H_{n,r} : P_n → Q_{n+1}, defined by the all-epimorphism coproduct prescription. -/
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

/-- Five prism face identities in a successor degree.

For n = d+1 and simplicial maps f,g : P → Q, require the two endpoint equations for H_{n,0}
and H_{n,n}, the early and late face-commutation equations for H_{n,r}, and equality of
adjacent prism operators after their common middle face. These equations hold on all of P_n
and use the preceding-degree operators H_{n−1}. -/
structure Faces (d : ℕ) : Prop where
/-- First endpoint face equation on the full simplicial term.

For n = d+1, require H_{n,0} ≫ d₀^Q = g_n as maps P_n → Q_n. -/
  zero : operator s p (d + 1) 0 (by omega) ≫ face Q (d + 1) 0 (by omega) = g.app (op ⦋d + 1⦌)
/-- Last endpoint face equation on the full simplicial term.

For n = d+1, require H_{n,n} ≫ d_{n+1}^Q = f_n as maps P_n → Q_n. -/
  last : operator s p (d + 1) (d + 1) (by omega) ≫ face Q (d + 1) (d + 2) (by omega) =
    f.app (op ⦋d + 1⦌)
/-- Early face equation on the full simplicial term.

For n = d+1, r ≤ n and j < r, require H_{n,r} ≫ d_j^Q = d_j^P ≫ H_{n−1,r−1}. The right-hand
side first takes the source face and then the preceding-degree prism operator. -/
  early : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : j < r),
    operator s p (d + 1) r hr ≫ face Q (d + 1) j (by omega) =
      face P d j (by omega) ≫ operator s p d (r - 1) (by omega)
/-- Late face equation on the full simplicial term.

For n = d+1, r ≤ n and r+1 < j ≤ n+1, require H_{n,r} ≫ d_j^Q = d_{j−1}^P ≫ H_{n−1,r}. The
source face index decreases by one. -/
  late : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : r + 1 < j) (hj' : j ≤ d + 2),
    operator s p (d + 1) r hr ≫ face Q (d + 1) j hj' =
      face P d (j - 1) (by omega) ≫ operator s p d r (by omega)
/-- Common-middle face equation on the full simplicial term.

For n = d+1 and r < n, require H_{n,r+1} ≫ d_{r+1}^Q = H_{n,r} ≫ d_{r+1}^Q. The two adjacent
prism operators agree after the same middle face. -/
  middle : ∀ (r : ℕ) (hr : r < d + 1),
    operator s p (d + 1) (r + 1) (by omega) ≫ face Q (d + 1) (r + 1) (by omega) =
      operator s p (d + 1) r (by omega) ≫ face Q (d + 1) (r + 1) (by omega)

/-- Prism face identities restricted to nondegenerate generators.

For n = d+1, require the five equations of Faces(d) only after precomposing each side by ι_n :
N_n → P_n. These are endpoint, early, late and common-middle conditions on the nondegenerate
summand. -/
structure FacesOnGenerators (d : ℕ) : Prop where
/-- First endpoint equation on nondegenerate generators.

For n = d+1, require ι_n ≫ H_{n,0} ≫ d₀^Q = ι_n ≫ g_n as maps N_n → Q_n. -/
  zero : s.ι (d + 1) ≫ (operator s p (d + 1) 0 (by omega) ≫ face Q (d + 1) 0 (by omega)) =
    s.ι (d + 1) ≫ g.app (op ⦋d + 1⦌)
/-- Last endpoint equation on nondegenerate generators.

For n = d+1, require ι_n ≫ H_{n,n} ≫ d_{n+1}^Q = ι_n ≫ f_n as maps N_n → Q_n. -/
  last : s.ι (d + 1) ≫ (operator s p (d + 1) (d + 1) (by omega) ≫
    face Q (d + 1) (d + 2) (by omega)) = s.ι (d + 1) ≫ f.app (op ⦋d + 1⦌)
/-- Early face equation on nondegenerate generators.

For n = d+1, r ≤ n and j < r, require ι_n ≫ H_{n,r} ≫ d_j^Q = ι_n ≫ d_j^P ≫ H_{n−1,r−1}. -/
  early : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : j < r),
    s.ι (d + 1) ≫ (operator s p (d + 1) r hr ≫ face Q (d + 1) j (by omega)) =
      s.ι (d + 1) ≫ (face P d j (by omega) ≫ operator s p d (r - 1) (by omega))
/-- Late face equation on nondegenerate generators.

For n = d+1, r ≤ n and r+1 < j ≤ n+1, require ι_n ≫ H_{n,r} ≫ d_j^Q = ι_n ≫ d_{j−1}^P ≫
H_{n−1,r}. -/
  late : ∀ (r : ℕ) (hr : r ≤ d + 1) (j : ℕ) (hj : r + 1 < j) (hj' : j ≤ d + 2),
    s.ι (d + 1) ≫ (operator s p (d + 1) r hr ≫ face Q (d + 1) j hj') =
      s.ι (d + 1) ≫ (face P d (j - 1) (by omega) ≫ operator s p d r (by omega))
/-- Common-middle face equation on nondegenerate generators.

For n = d+1 and r < n, require ι_n ≫ H_{n,r+1} ≫ d_{r+1}^Q = ι_n ≫ H_{n,r} ≫ d_{r+1}^Q. -/
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

/-- Descent of prism face laws to the next simplicial degree.

For the splitting-descended operators H, Faces(d) and FacesOnGenerators(d+1) imply Faces(d+1).
Restriction to N_{d+2} is the given generator equation, while restriction along each
degeneracy reduces to the face laws in degree d+1. -/
theorem descend (old : Faces s p f g d) (new : FacesOnGenerators s p f g (d + 1)) :
    Faces s p f g (d + 1) where
  zero := zero_descend s p f g old new
  last := last_descend s p f g old new
  early := early_descend s p f g old new
  late := late_descend s p f g old new
  middle := middle_descend s p f g old new

/-- Descent of a prism augmentation equation.

Let ε_P : P → const(A) and ε_Q : Q → const(A) be augmentations. Suppose H_{d+1,r} ≫ ε_Q,d+2 =
ε_P,d+1 for every r ≤ d+1, and the equation H_{d+2,r} ≫ ε_Q,d+3 = ε_P,d+2 holds after ι_{d+2}
for every r ≤ d+2. Then the latter equation holds on all of P_{d+2}, by splitting
extensionality and degeneracy compatibility. -/
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
