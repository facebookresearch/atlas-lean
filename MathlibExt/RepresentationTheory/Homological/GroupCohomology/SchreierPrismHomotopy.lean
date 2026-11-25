/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitrary
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferIndependence
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.Grp.Adjunctions

/-!
# The finite signed Schreier prism

The prism inserts the actual change-of-representative factor between a prefix
of the first Schreier factor tuple and a suffix of the second one. Its finite
signed sum is the proposed explicit cochain homotopy for transversal change.
All scalar, group and coefficient universes are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped BigOperators Simplicial
open CategoryTheory Opposite SimplexCategory

universe r g v

namespace SchreierPrism

/-- The homogeneous prism repeats the middle vertex while switching between two vertex maps. -/
def vertices {X : Type g} {n : ℕ} (a b : Fin (n + 1) → X)
    (i : Fin (n + 1)) (j : Fin (n + 2)) : X :=
  if h : (j : ℕ) ≤ (i : ℕ) then a ⟨j, lt_of_le_of_lt h i.isLt⟩
  else b ⟨(j : ℕ) - 1, by omega⟩

/-- The inserted prism coordinate is the original first vertex. -/
theorem vertices_inserted {X : Type g} {n : ℕ} (a b : Fin (n + 1) → X)
    (i : Fin (n + 1)) : vertices a b i i.castSucc = a i := by
  simp only [vertices, Fin.val_castSucc, le_refl, dite_true]

private theorem succAboveValue {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j : ℕ) = if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ) + 1 := by
  by_cases h : (j : ℕ) < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

private theorem predAboveValue {n : ℕ} (i : Fin n) (j : Fin (n + 1)) :
    (i.predAbove j : ℕ) = if (i : ℕ) < (j : ℕ) then (j : ℕ) - 1 else (j : ℕ) := by
  by_cases h : (i : ℕ) < j
  · rw [Fin.predAbove_of_castSucc_lt _ _ h, ite_eq_left h]
    rfl
  · rw [Fin.predAbove_of_le_castSucc _ _ (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

private theorem vertices_zero {X : Type g} {n : ℕ}
    (a b : Fin (n + 1) → X) (j : Fin (n + 1)) :
    vertices a b 0 j.succ = b j := by
  unfold vertices
  split_ifs with h
  · have : (j : ℕ) + 1 ≤ 0 := h
    omega
  · congr 1

private theorem vertices_last {X : Type g} {n : ℕ}
    (a b : Fin (n + 1) → X) (j : Fin (n + 1)) :
    vertices a b (Fin.last n) j.castSucc = a j := by
  unfold vertices
  split_ifs with h
  · congr 1
  · have : ¬(j : ℕ) ≤ n := h
    omega

private theorem vertices_face_before {X : Type g} {n : ℕ}
    (a b : Fin (n + 2) → X) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (k : Fin (n + 2)) :
    vertices a b j.succ (i.castSucc.succAbove k) =
      vertices (a ∘ i.succAbove) (b ∘ i.succAbove) j k := by
  have hi : (i : ℕ) ≤ j := hij
  by_cases hki : (k : ℕ) < i
  · rw [Fin.succAbove_of_castSucc_lt i.castSucc k hki]
    have hkj : (k : ℕ) ≤ j := by omega
    unfold vertices
    rw [dite_eq_left (by simpa only [Fin.val_castSucc, Fin.val_succ] using
      (show (k : ℕ) ≤ (j : ℕ) + 1 by omega)), dite_eq_left hkj]
    change a k = a (i.succAbove ⟨k, by omega⟩)
    rw [Fin.succAbove_of_castSucc_lt _ _ hki]
    apply congrArg a
    apply Fin.ext
    rfl
  · have hik : (i : ℕ) ≤ k := by omega
    rw [Fin.succAbove_of_le_castSucc i.castSucc k hik]
    by_cases hkj : (k : ℕ) ≤ j
    · unfold vertices
      rw [dite_eq_left (by change (k : ℕ) + 1 ≤ (j : ℕ) + 1; omega), dite_eq_left hkj]
      apply congrArg a
      apply Fin.ext
      rw [succAboveValue]
      simp only [Fin.val_succ]
      rw [ite_eq_right (by omega)]
    · have hjk : (j : ℕ) < k := by omega
      unfold vertices
      rw [dite_eq_right (by change ¬(k : ℕ) + 1 ≤ (j : ℕ) + 1; omega), dite_eq_right hkj]
      apply congrArg b
      apply Fin.ext
      rw [succAboveValue]
      simp only [Fin.val_succ]
      rw [ite_eq_right (by omega)]
      omega

private theorem vertices_face_middle {X : Type g} {n : ℕ}
    (a b : Fin (n + 2) → X) (j : Fin (n + 1)) (k : Fin (n + 2)) :
    vertices a b j.succ (j.castSucc.succ.succAbove k) =
      vertices a b j.castSucc (j.castSucc.succ.succAbove k) := by
  by_cases hk : (k : ℕ) ≤ j
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change (k : ℕ) < (j : ℕ) + 1; omega)]
    unfold vertices
    rw [dite_eq_left (by change (k : ℕ) ≤ (j : ℕ) + 1; omega),
      dite_eq_left (by exact hk)]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by
      change (j : ℕ) + 1 ≤ k; omega)]
    unfold vertices
    rw [dite_eq_right (by change ¬(k : ℕ) + 1 ≤ (j : ℕ) + 1; omega),
      dite_eq_right (by change ¬(k : ℕ) + 1 ≤ j; omega)]

private theorem vertices_face_after {X : Type g} {n : ℕ}
    (a b : Fin (n + 2) → X) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (k : Fin (n + 2)) :
    vertices a b j.castSucc (i.succ.succAbove k) =
      vertices (a ∘ i.succAbove) (b ∘ i.succAbove) j k := by
  have hi : (j : ℕ) < i := hji
  by_cases hkj : (k : ℕ) ≤ j
  · have hki : (k : ℕ) < i := by omega
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change (k : ℕ) < (i : ℕ) + 1; omega)]
    unfold vertices
    rw [dite_eq_left (by exact hkj), dite_eq_left hkj]
    apply congrArg a
    apply Fin.ext
    rw [succAboveValue, ite_eq_left (by exact hki)]
    rfl
  · have hjk : (j : ℕ) < k := by omega
    by_cases hki : (k : ℕ) ≤ i
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by
        change (k : ℕ) < (i : ℕ) + 1; omega)]
      unfold vertices
      rw [dite_eq_right (by exact hkj), dite_eq_right hkj]
      apply congrArg b
      apply Fin.ext
      rw [succAboveValue, ite_eq_left (by change (k : ℕ) - 1 < i; omega)]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (by
        change (i : ℕ) + 1 ≤ k; omega)]
      unfold vertices
      rw [dite_eq_right (by change ¬(k : ℕ) + 1 ≤ j; omega), dite_eq_right hkj]
      apply congrArg b
      apply Fin.ext
      rw [succAboveValue, ite_eq_right (by change ¬(k : ℕ) - 1 < i; omega)]
      simp only [Fin.val_succ]
      omega

private theorem vertices_degeneracy_before {X : Type g} {n : ℕ}
    (a b : Fin (n + 1) → X) (i j : Fin (n + 1)) (hij : i ≤ j)
    (k : Fin (n + 3)) :
    vertices a b j (i.castSucc.predAbove k) =
      vertices (a ∘ i.predAbove) (b ∘ i.predAbove) j.succ k := by
  have hi : (i : ℕ) ≤ j := hij
  by_cases hki : (k : ℕ) ≤ i
  · rw [Fin.predAbove_of_le_castSucc _ _ (by exact hki)]
    unfold vertices
    rw [dite_eq_left (by change (k : ℕ) ≤ j; omega),
      dite_eq_left (by change (k : ℕ) ≤ (j : ℕ) + 1; omega)]
    apply congrArg a
    apply Fin.ext
    rw [predAboveValue, ite_eq_right (by change ¬(i : ℕ) < k; omega)]
    rfl
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by change (i : ℕ) < k; omega)]
    by_cases hkj : (k : ℕ) ≤ (j : ℕ) + 1
    · unfold vertices
      rw [dite_eq_left (by change (k : ℕ) - 1 ≤ j; omega),
          dite_eq_left (by change (k : ℕ) ≤ (j : ℕ) + 1; exact hkj)]
      apply congrArg a
      apply Fin.ext
      rw [predAboveValue, ite_eq_left (by change (i : ℕ) < k; omega)]
      rfl
    · unfold vertices
      rw [dite_eq_right (by change ¬(k : ℕ) - 1 ≤ j; omega),
          dite_eq_right (by change ¬(k : ℕ) ≤ (j : ℕ) + 1; exact hkj)]
      apply congrArg b
      apply Fin.ext
      rw [predAboveValue, ite_eq_left (by change (i : ℕ) < (k : ℕ) - 1; omega)]
      rfl

private theorem vertices_degeneracy_after {X : Type g} {n : ℕ}
    (a b : Fin (n + 1) → X) (i j : Fin (n + 1)) (hji : j ≤ i)
    (k : Fin (n + 3)) :
    vertices a b j (i.succ.predAbove k) =
      vertices (a ∘ i.predAbove) (b ∘ i.predAbove) j.castSucc k := by
  have hi : (j : ℕ) ≤ i := hji
  by_cases hkj : (k : ℕ) ≤ j
  · rw [Fin.predAbove_of_le_castSucc _ _ (by change (k : ℕ) ≤ (i : ℕ) + 1; omega)]
    unfold vertices
    rw [dite_eq_left (by change (k : ℕ) ≤ (j : ℕ); exact hkj),
        dite_eq_left (by change (k : ℕ) ≤ (j : ℕ); exact hkj)]
    apply congrArg a
    apply Fin.ext
    rw [predAboveValue, ite_eq_right (by change ¬(i : ℕ) < k; omega)]
    rfl
  · by_cases hki : (k : ℕ) ≤ (i : ℕ) + 1
    · rw [Fin.predAbove_of_le_castSucc _ _ hki]
      unfold vertices
      rw [dite_eq_right (by change ¬(k : ℕ) ≤ (j : ℕ); exact hkj),
          dite_eq_right (by change ¬(k : ℕ) ≤ (j : ℕ); exact hkj)]
      apply congrArg b
      apply Fin.ext
      rw [predAboveValue, ite_eq_right (by change ¬(i : ℕ) < (k : ℕ) - 1; omega)]
      rfl
    · rw [Fin.predAbove_of_castSucc_lt _ _ (by change (i : ℕ) + 1 < k; omega)]
      unfold vertices
      rw [dite_eq_right (by change ¬(k : ℕ) - 1 ≤ j; omega),
          dite_eq_right (by change ¬(k : ℕ) ≤ (j : ℕ); exact hkj)]
      apply congrArg b
      apply Fin.ext
      rw [predAboveValue, ite_eq_left (by change (i : ℕ) < (k : ℕ) - 1; omega)]
      rfl

private def tupleSimplicial (X : Type g) : SimplicialObject (Type g) where
  obj n := Fin (n.unop.len + 1) → X
  map f := ↾fun x => x ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

private def tupleMap {X Y : Type g} (f : X → Y) : tupleSimplicial X ⟶ tupleSimplicial Y where
  app _ := ↾fun x i => f (x i)

private def tuplePrismHomotopy {X Y : Type g} (f g : X → Y) :
    SimplicialObject.Homotopy (tupleMap f) (tupleMap g) where
  h i := ↾fun x => vertices (f ∘ x) (g ∘ x) i
  h_zero_comp_δ_zero n := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext j
    change vertices (f ∘ x) (g ∘ x) 0 j.succ = g (x j)
    exact vertices_zero _ _ _
  h_last_comp_δ_last n := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext j
    change vertices (f ∘ x) (g ∘ x) (Fin.last n)
      ((Fin.last (n + 1)).succAbove j) = f (x j)
    rw [Fin.succAbove_last]
    exact vertices_last (f ∘ x) (g ∘ x) j
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext k
    change vertices (f ∘ x) (g ∘ x) j.succ (i.castSucc.succAbove k) =
      vertices (f ∘ (x ∘ i.succAbove)) (g ∘ (x ∘ i.succAbove)) j k
    exact vertices_face_before _ _ i j hij k
  h_succ_comp_δ_castSucc_succ j := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext k
    change vertices (f ∘ x) (g ∘ x) j.succ (j.castSucc.succ.succAbove k) =
      vertices (f ∘ x) (g ∘ x) j.castSucc (j.castSucc.succ.succAbove k)
    exact vertices_face_middle _ _ j k
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext k
    change vertices (f ∘ x) (g ∘ x) j.castSucc (i.succ.succAbove k) =
      vertices (f ∘ (x ∘ i.succAbove)) (g ∘ (x ∘ i.succAbove)) j k
    exact vertices_face_after _ _ i j hji k
  h_comp_σ_castSucc_of_le i j hij := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext k
    change vertices (f ∘ x) (g ∘ x) j (i.castSucc.predAbove k) =
      vertices (f ∘ (x ∘ i.predAbove)) (g ∘ (x ∘ i.predAbove)) j.succ k
    exact vertices_degeneracy_before _ _ i j hij k
  h_comp_σ_succ_of_lt i j hji := by
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    funext k
    change vertices (f ∘ x) (g ∘ x) j (i.succ.predAbove k) =
      vertices (f ∘ (x ∘ i.predAbove)) (g ∘ (x ∘ i.predAbove)) j.castSucc k
    exact vertices_degeneracy_after _ _ i j hji k

private theorem abelian_sum_apply {ι : Type*} {P Q : AddCommGrpCat.{g}}
    (s : Finset ι) (f : ι → (P ⟶ Q)) (x : P) :
    (s.sum f) x = s.sum (fun i => f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

private theorem abelian_hom_sum {ι : Type*} {P Q : AddCommGrpCat.{g}}
    (s : Finset ι) (f : ι → (P ⟶ Q)) :
    (s.sum f).hom = s.sum (fun i => (f i).hom) := by
  exact map_sum (AddCommGrpCat.homAddEquiv (M := P) (N := Q)).toAddMonoidHom f s

private theorem abelian_neg_apply {P Q : AddCommGrpCat.{g}} (f : P ⟶ Q) (x : P) :
    (-f).hom x = -(f.hom x) := rfl

private theorem abelian_zsmul_apply {P Q : AddCommGrpCat.{g}}
    (a : ℤ) (f : P ⟶ Q) (x : P) : (a • f).hom x = a • f.hom x := rfl

private def freeTuplePrism {X Y : Type g} (f g : X → Y) (n : ℕ) :
    AddCommGrpCat.of (FreeAbelianGroup (Fin (n + 1) → X)) ⟶
      AddCommGrpCat.of (FreeAbelianGroup (Fin (n + 2) → Y)) :=
  -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
    AddCommGrpCat.ofHom (FreeAbelianGroup.map
      (fun x => vertices (f ∘ x) (g ∘ x) i))

private theorem freeTuplePrism_apply {X Y : Type g} (f g : X → Y) (n : ℕ)
    (x : Fin (n + 1) → X) :
    (freeTuplePrism f g n).hom (FreeAbelianGroup.of x) =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        FreeAbelianGroup.of (vertices (f ∘ x) (g ∘ x) i) := by
  change (-(∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
    AddCommGrpCat.ofHom (FreeAbelianGroup.map (fun x => vertices (f ∘ x) (g ∘ x) i))))
      (FreeAbelianGroup.of x) = _
  rw [abelian_neg_apply, abelian_sum_apply]
  congr 1

private def freeTupleD (X : Type g) (n : ℕ) :
    AddCommGrpCat.of (FreeAbelianGroup (Fin (n + 2) → X)) ⟶
      AddCommGrpCat.of (FreeAbelianGroup (Fin (n + 1) → X)) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    AddCommGrpCat.ofHom (FreeAbelianGroup.map (fun x => x ∘ i.succAbove))

private theorem freeTupleD_apply (X : Type g) (n : ℕ) (x : Fin (n + 2) → X) :
    (freeTupleD X n).hom (FreeAbelianGroup.of x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (x ∘ i.succAbove) := by
  change freeTupleD X n (FreeAbelianGroup.of x) = _
  rw [freeTupleD, abelian_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [abelian_zsmul_apply]
  exact congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (FreeAbelianGroup.map_of_apply x)

/-- The finite homogeneous prism satisfies the actual alternating boundary identity. -/
theorem homogeneous_prism_identity_succ
    {X Y : Type g} {M : Type v} [AddCommGroup M]
    (f g : X → Y) (n : ℕ) (c : (Fin (n + 2) → Y) → M)
    (x : Fin (n + 2) → X) :
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        c (vertices (f ∘ (x ∘ j.succAbove)) (g ∘ (x ∘ j.succAbove)) i))) +
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
          c (vertices (f ∘ x) (g ∘ x) i ∘ j.succAbove))) =
      c (g ∘ x) - c (f ∘ x) := by
  let H := (tuplePrismHomotopy f g).whiskerRight (AddCommGrpCat.free.{g})
  let h := H.toChainHomotopy
  have hc := h.comm (n + 1)
  rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)] at hc
  have hP : h.hom n (n + 1) = freeTuplePrism f g n := by
    dsimp only [h, SimplicialObject.Homotopy.toChainHomotopy]
    rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    rfl
  have hQ : h.hom (n + 1) (n + 2) = freeTuplePrism f g (n + 1) := by
    dsimp only [h, SimplicialObject.Homotopy.toChainHomotopy]
    rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    rfl
  rw [hP, hQ] at hc
  have hDX : ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).obj
      (((SimplicialObject.whiskering (Type g) AddCommGrpCat).obj
        AddCommGrpCat.free).obj (tupleSimplicial X))).d (n + 1) n =
        freeTupleD X n := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
    rfl
  have hDY : ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).obj
      (((SimplicialObject.whiskering (Type g) AddCommGrpCat).obj
        AddCommGrpCat.free).obj (tupleSimplicial Y))).d (n + 2) (n + 1) =
        freeTupleD Y (n + 1) := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
    rfl
  rw [hDX, hDY, AlgebraicTopology.alternatingFaceMapComplex_map_f,
    AlgebraicTopology.alternatingFaceMapComplex_map_f] at hc
  have hv := congrArg (fun q => q.hom (FreeAbelianGroup.of x)) hc
  change FreeAbelianGroup.map (fun x i => f (x i)) (FreeAbelianGroup.of x) =
    freeTuplePrism f g n (freeTupleD X n (FreeAbelianGroup.of x)) +
      freeTupleD Y (n + 1) (freeTuplePrism f g (n + 1) (FreeAbelianGroup.of x)) +
        FreeAbelianGroup.map (fun x i => g (x i)) (FreeAbelianGroup.of x) at hv
  rw [freeTupleD_apply, freeTuplePrism_apply] at hv
  have heval := congrArg (fun z => FreeAbelianGroup.lift c z) hv
  simp only [FreeAbelianGroup.map_of_apply, map_add, map_neg, map_sum, map_zsmul,
    FreeAbelianGroup.lift_apply_of] at heval
  have hpval (y : Fin (n + 1) → X) :
      FreeAbelianGroup.lift c ((freeTuplePrism f g n).hom (FreeAbelianGroup.of y)) =
        -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
          c (vertices (f ∘ y) (g ∘ y) i) := by
    rw [freeTuplePrism_apply]
    simp only [map_neg, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of]
  have hdval (y : Fin (n + 3) → Y) :
      FreeAbelianGroup.lift c ((freeTupleD Y (n + 1)).hom (FreeAbelianGroup.of y)) =
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • c (y ∘ j.succAbove) := by
    rw [freeTupleD_apply]
    simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of]
  have hs1 := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (j : Fin (n + 2)) _ =>
      congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z) (hpval (x ∘ j.succAbove)))
  have hs2 := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin (n + 2)) _ =>
      congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z)
        (hdval (vertices (f ∘ x) (g ∘ x) i)))
  rw [hs1, hs2] at heval
  simp only [smul_neg, Finset.sum_neg_distrib] at heval
  apply eq_sub_iff_add_eq.mpr
  dsimp only [Function.comp_def] at heval ⊢
  rw [heval]
  abel

end SchreierPrism

namespace Subgroup.RightTransversal

variable {G : Type g} [Group G] {H : Subgroup G}

/-- The actual change factors at the successive vertices of a Schreier scan. -/
def schreierChangeScan {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) : Fin (n + 1) → H :=
  fun i => T.changeFactor U (T.schreierRepScan t tuple i)

/-- Matching actual representatives commutes with every prefix-product scan. -/
theorem schreierChangeRep_scan {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin (n + 1)) :
    T.changeRep U (T.schreierRepScan t tuple i) =
      U.schreierRepScan (T.changeRep U t) tuple i :=
  T.changeRep_schreierRep U t (Fin.partialProd tuple i)

/-- The actual factor tuples and change scan satisfy the commuting-square identity. -/
theorem schreierChangeScan_factor {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin n) :
    T.schreierFactorTuple t tuple i * T.schreierChangeScan U t tuple i.succ =
      T.schreierChangeScan U t tuple i.castSucc *
        U.schreierFactorTuple (T.changeRep U t) tuple i := by
  unfold schreierFactorTuple schreierChangeScan
  rw [T.schreierRepScan_get_succ]
  rw [T.schreierFactor_mul_changeFactor U]
  rw [T.schreierChangeRep_scan U]

/-- The actual prism tuple: first factors, inserted change factor, then second factors. -/
def schreierPrismTuple {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin (n + 1)) : Fin (n + 1) → H :=
  Fin.insertNth i (T.schreierChangeScan U t tuple i)
    (fun j => if (j : ℕ) < (i : ℕ) then T.schreierFactorTuple t tuple j
      else U.schreierFactorTuple (T.changeRep U t) tuple j)

/-- The inserted coordinate is exactly the original change-of-representative factor. -/
theorem schreierPrismTuple_inserted {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin (n + 1)) :
    T.schreierPrismTuple U t tuple i i = T.schreierChangeScan U t tuple i :=
  Fin.insertNth_apply_same _ _ _

/-- Away from the inserted coordinate the prism retains the actual first or second factor. -/
theorem schreierPrismTuple_other {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin (n + 1)) (j : Fin n) :
    T.schreierPrismTuple U t tuple i (i.succAbove j) =
      if (j : ℕ) < (i : ℕ) then T.schreierFactorTuple t tuple j
      else U.schreierFactorTuple (T.changeRep U t) tuple j :=
  Fin.insertNth_apply_succAbove _ _ _ _

/-- Consecutive subgroup vertices recover the original Schreier factor tuple. -/
theorem schreierFactor_partialProd_difference {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin n) :
    (T.schreierFactor t (Fin.partialProd tuple i.castSucc))⁻¹ *
        T.schreierFactor t (Fin.partialProd tuple i.succ) =
      T.schreierFactorTuple t tuple i := by
  rw [Fin.partialProd_succ, T.schreierFactor_mul]
  change (T.schreierFactor t (Fin.partialProd tuple i.castSucc))⁻¹ *
    (T.schreierFactor t (Fin.partialProd tuple i.castSucc) *
      T.schreierFactorTuple t tuple i) = _
  exact inv_mul_cancel_left _ _

/-- The homogeneous vertex prism has exactly the existing inserted Schreier factor tuple. -/
theorem schreierPrismTuple_eq_differences {n : ℕ} (T U : H.RightTransversal)
    (t : (T : Set G)) (tuple : Fin n → G) (i : Fin (n + 1)) :
    let a : Fin (n + 1) → H := fun j => T.schreierFactor t (Fin.partialProd tuple j)
    let b : Fin (n + 1) → H := fun j =>
      T.changeFactor U t * U.schreierFactor (T.changeRep U t) (Fin.partialProd tuple j)
    (fun j : Fin (n + 1) =>
      (SchreierPrism.vertices a b i j.castSucc)⁻¹ * SchreierPrism.vertices a b i j.succ) =
        T.schreierPrismTuple U t tuple i := by
  intro a b
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨k, rfl⟩
  · subst j
    rw [schreierPrismTuple_inserted, SchreierPrism.vertices_inserted]
    have hb : SchreierPrism.vertices a b i i.succ = b i := by
      simp only [SchreierPrism.vertices,
          Fin.val_succ, Nat.not_succ_le_self, dite_false, Nat.add_sub_cancel_right]
    rw [hb]
    have h := T.schreierFactor_mul_changeFactor U t (Fin.partialProd tuple i)
    change a i * T.schreierChangeScan U t tuple i = b i at h
    rw [← h]
    exact inv_mul_cancel_left _ _
  · rw [schreierPrismTuple_other]
    by_cases hki : (k : ℕ) < (i : ℕ)
    · rw [ite_eq_left hki, Fin.succAbove_of_castSucc_lt i k hki]
      have hk0 : (k.castSucc.castSucc : ℕ) ≤ (i : ℕ) := Nat.le_of_lt hki
      have hk1 : (k.castSucc.succ : ℕ) ≤ (i : ℕ) := Nat.succ_le_of_lt hki
      rw [SchreierPrism.vertices, dite_eq_left hk0, SchreierPrism.vertices, dite_eq_left hk1]
      change (a k.castSucc)⁻¹ * a k.succ = T.schreierFactorTuple t tuple k
      exact schreierFactor_partialProd_difference T t tuple k
    · rw [ite_eq_right hki, Fin.succAbove_of_le_castSucc i k (Nat.le_of_not_gt hki)]
      have hk0 : ¬(k.succ.castSucc : ℕ) ≤ (i : ℕ) := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hk1 : ¬(k.succ.succ : ℕ) ≤ (i : ℕ) := by
        simp only [Fin.val_succ]
        omega
      rw [SchreierPrism.vertices, dite_eq_right hk0, SchreierPrism.vertices, dite_eq_right hk1]
      change (b k.castSucc)⁻¹ * b k.succ =
        U.schreierFactorTuple (T.changeRep U t) tuple k
      change (T.changeFactor U t *
          U.schreierFactor (T.changeRep U t) (Fin.partialProd tuple k.castSucc))⁻¹ *
        (T.changeFactor U t *
          U.schreierFactor (T.changeRep U t) (Fin.partialProd tuple k.succ)) = _
      rw [mul_inv_rev]
      simp only [mul_assoc, inv_mul_cancel_left]
      exact schreierFactor_partialProd_difference U (T.changeRep U t) tuple k

end Subgroup.RightTransversal

namespace groupCohomology

variable {R : Type r} [Ring R] {G : Type g} [Group G] {M : Type v}
  [AddCommGroup M] [Module R M] {H : Subgroup G}

private def homogeneousValue {J : Type g} [Group J] (rho : Representation R J M)
    (n : ℕ) (f : (Fin n → J) → M) (y : Fin (n + 1) → J) : M :=
  rho (y 0) (f (fun i => (y i.castSucc)⁻¹ * y i.succ))

private theorem homogeneousValue_mul {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M)
    (h : J) (y : Fin (n + 1) → J) :
    homogeneousValue rho n f (fun i => h * y i) = rho h (homogeneousValue rho n f y) := by
  have hd : (fun i : Fin n => (h * y i.castSucc)⁻¹ * (h * y i.succ)) =
      (fun i : Fin n => (y i.castSucc)⁻¹ * y i.succ) := by
    funext i
    group
  unfold homogeneousValue
  rw [hd, map_mul]
  rfl

private theorem homogeneousValue_partialProd {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M) (tuple : Fin n → J) :
    homogeneousValue rho n f (Fin.partialProd tuple) = f tuple := by
  have hd : (fun i : Fin n => (Fin.partialProd tuple i.castSucc)⁻¹ *
      Fin.partialProd tuple i.succ) = tuple := by
    funext i
    exact Fin.partialProd_right_inv tuple i
  unfold homogeneousValue
  rw [Fin.partialProd_zero, hd, map_one]
  rfl

private theorem homogeneousValue_partialProd_face_zero {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M)
    (tuple : Fin (n + 1) → J) :
    homogeneousValue rho n f (Fin.partialProd tuple ∘ (0 : Fin (n + 2)).succAbove) =
      rho (tuple 0) (f (Fin.tail tuple)) := by
  have ht : Fin.partialProd tuple ∘ (0 : Fin (n + 2)).succAbove =
      (fun i => tuple 0 * Fin.partialProd (Fin.tail tuple) i) := by
    funext i
    simpa only [Function.comp_def, Fin.zero_succAbove] using Fin.partialProd_succ' tuple i
  rw [ht, homogeneousValue_mul, homogeneousValue_partialProd]

private theorem homogeneousValue_partialProd_face_succ {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M)
    (tuple : Fin (n + 1) → J) (j : Fin (n + 1)) :
    homogeneousValue rho n f (Fin.partialProd tuple ∘ j.succ.succAbove) =
      f (Fin.contractNth j (· * ·) tuple) := by
  rw [← Fin.partialProd_contractNth, homogeneousValue_partialProd]

private theorem homogeneousValue_partialProd_d {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M)
    (tuple : Fin (n + 1) → J) :
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      homogeneousValue rho n f (Fin.partialProd tuple ∘ j.succAbove)) =
    rho (tuple 0) (f (Fin.tail tuple)) +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        f (Fin.contractNth j (· * ·) tuple) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  rw [homogeneousValue_partialProd_face_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [homogeneousValue_partialProd_face_succ]

private theorem homogeneousValue_d {J : Type g} [Group J]
    (rho : Representation R J M) (n : ℕ) (f : (Fin n → J) → M)
    (y : Fin (n + 2) → J) :
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      homogeneousValue rho n f (y ∘ j.succAbove)) =
      homogeneousValue rho (n + 1)
        (fun tuple => rho (tuple 0) (f (Fin.tail tuple)) +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) tuple)) y := by
  let tuple : Fin (n + 1) → J := fun i => (y i.castSucc)⁻¹ * y i.succ
  have hy : (fun i => y 0 * Fin.partialProd tuple i) = y :=
    Fin.partialProd_left_inv y
  have hv (j : Fin (n + 2)) :
      homogeneousValue rho n f (y ∘ j.succAbove) =
        rho (y 0) (homogeneousValue rho n f (Fin.partialProd tuple ∘ j.succAbove)) := by
    conv_lhs => rw [← hy]
    exact homogeneousValue_mul rho n f (y 0) _
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      homogeneousValue rho n f (y ∘ j.succAbove)) =
    rho (y 0) (rho (tuple 0) (f (Fin.tail tuple)) +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        f (Fin.contractNth j (· * ·) tuple))
  rw [← homogeneousValue_partialProd_d rho n f tuple, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hv, map_zsmul]

/-- A finite-index subgroup has finitely many actual representatives in each right transversal. -/
local instance prismTransversalFintype (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T : Set G) := @Fintype.ofFinite (T : Set G) T.2.finite_right

private theorem vertices_mul {J : Type g} [Group J] {n : ℕ}
    (a b : Fin (n + 1) → J) (h : J) (i : Fin (n + 1)) :
    SchreierPrism.vertices (fun j => h * a j) (fun j => h * b j) i =
      (fun j => h * SchreierPrism.vertices a b i j) := by
  funext j
  unfold SchreierPrism.vertices
  split_ifs <;> rfl

private def prismAt (rho : Representation R G M) (T U : H.RightTransversal)
    (n : ℕ) (f : (Fin (n + 1) → H) → M) (t : (T : Set G))
    (x : Fin (n + 1) → G) : M :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
    homogeneousValue (rho.comp H.subtype) (n + 1) f
      (SchreierPrism.vertices (fun j => T.schreierFactor t (x j))
        (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (x j)) i)

private theorem prismAt_partialProd (rho : Representation R G M)
    (T U : H.RightTransversal) (n : ℕ) (f : (Fin (n + 1) → H) → M)
    (t : (T : Set G)) (tuple : Fin n → G) :
    prismAt rho T U n f t (Fin.partialProd tuple) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        f (T.schreierPrismTuple U t tuple i) := by
  unfold prismAt
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  let a : Fin (n + 1) → H := fun j => T.schreierFactor t (Fin.partialProd tuple j)
  let b : Fin (n + 1) → H := fun j =>
    T.changeFactor U t * U.schreierFactor (T.changeRep U t) (Fin.partialProd tuple j)
  have hzero : SchreierPrism.vertices a b i 0 = 1 := by
    simp only [SchreierPrism.vertices, Fin.val_zero, Nat.zero_le]
    exact (T.schreierFactor_one t)
  have hd := T.schreierPrismTuple_eq_differences U t tuple i
  change (fun j : Fin (n + 1) =>
    (SchreierPrism.vertices a b i j.castSucc)⁻¹ *
      SchreierPrism.vertices a b i j.succ) = T.schreierPrismTuple U t tuple i at hd
  change homogeneousValue (rho.comp H.subtype) (n + 1) f
    (SchreierPrism.vertices a b i) = _
  unfold homogeneousValue
  rw [hzero, hd, map_one]
  rfl

private theorem prismAt_mul (rho : Representation R G M) (T U : H.RightTransversal)
    (n : ℕ) (f : (Fin (n + 1) → H) → M) (t : (T : Set G))
    (h : G) (x : Fin (n + 1) → G) :
    prismAt rho T U n f t (fun j => h * x j) =
      rho (T.schreierFactor t h : G) (prismAt rho T U n f (T.schreierRep t h) x) := by
  let a : H := T.schreierFactor t h
  let t' := T.schreierRep t h
  have hA : (fun j => T.schreierFactor t (h * x j)) =
      (fun j => a * T.schreierFactor t' (x j)) := by
    funext j
    exact T.schreierFactor_mul t h (x j)
  have hB : (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (h * x j)) =
      (fun j => a * (T.changeFactor U t' * U.schreierFactor (T.changeRep U t') (x j))) := by
    funext j
    rw [U.schreierFactor_mul, ← mul_assoc,
      ← T.schreierFactor_mul_changeFactor U t h, T.changeRep_schreierRep U t h]
    exact mul_assoc _ _ _
  unfold prismAt
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  rw [hA, hB, vertices_mul]
  exact homogeneousValue_mul (rho.comp H.subtype) (n + 1) f a _

private def homogeneousPrism (rho : Representation R G M) (T U : H.RightTransversal)
    [H.FiniteIndex] (n : ℕ) (f : (Fin (n + 1) → H) → M)
    (x : Fin (n + 1) → G) : M :=
  ∑ t : (T : Set G), rho (t : G)⁻¹ (prismAt rho T U n f t x)

private theorem homogeneousPrism_mul (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin (n + 1) → H) → M) (h : G) (x : Fin (n + 1) → G) :
    homogeneousPrism rho T U n f (fun j => h * x j) =
      rho h (homogeneousPrism rho T U n f x) := by
  have ht (t : (T : Set G)) :
      rho (t : G)⁻¹ (prismAt rho T U n f t (fun j => h * x j)) =
        rho h (rho (T.schreierRep t h : G)⁻¹
          (prismAt rho T U n f (T.schreierRep t h) x)) := by
    rw [prismAt_mul, ← Module.End.mul_apply, ← map_mul, T.inv_mul_schreierFactor]
    rw [map_mul]
    rfl
  unfold homogeneousPrism
  rw [map_sum]
  calc
    _ = ∑ t : (T : Set G), rho h (rho (T.schreierRep t h : G)⁻¹
        (prismAt rho T U n f (T.schreierRep t h) x)) :=
      Finset.sum_congr rfl (fun t _ => ht t)
    _ = ∑ t : (T : Set G), rho h (rho (t : G)⁻¹ (prismAt rho T U n f t x)) :=
      (T.schreierRepEquiv h).sum_comp
        (fun t : (T : Set G) => rho h (rho (t : G)⁻¹ (prismAt rho T U n f t x)))

/-- The actual arbitrary-degree finite signed prism cochain, with independent universes. -/
def schreierPrism (rho : Representation R G M) (T U : H.RightTransversal)
    [H.FiniteIndex] (n : ℕ) : ((Fin (n + 1) → H) → M) →ₗ[R] ((Fin n → G) → M) where
  toFun f tuple := ∑ t : (T : Set G), rho (t : G)⁻¹
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (T.schreierPrismTuple U t tuple i))
  map_add' f h := by
    ext tuple
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  map_smul' a f := by
    ext tuple
    simp only [Pi.smul_apply, RingHom.id_apply]
    simp_rw [smul_comm ((-1 : ℤ) ^ _) a]
    rw [Finset.smul_sum]
    congr 1
    ext t
    rw [← Finset.smul_sum, map_smul]

/-- Evaluation of the prism is the literal finite signed sum over actual factor tuples. -/
theorem schreierPrism_apply (rho : Representation R G M) (T U : H.RightTransversal)
    [H.FiniteIndex] (n : ℕ) (f : (Fin (n + 1) → H) → M) (tuple : Fin n → G) :
    schreierPrism rho T U n f tuple = ∑ t : (T : Set G), rho (t : G)⁻¹
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (T.schreierPrismTuple U t tuple i)) := rfl


private theorem homogeneousPrism_partialProd (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin (n + 1) → H) → M) (tuple : Fin n → G) :
    homogeneousPrism rho T U n f (Fin.partialProd tuple) =
      schreierPrism rho T U n f tuple := by
  unfold homogeneousPrism
  rw [schreierPrism_apply]
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (rho (t : G)⁻¹) (prismAt_partialProd rho T U n f t tuple)

private theorem homogeneousPrism_eq_homogeneousValue (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin (n + 1) → H) → M) (x : Fin (n + 1) → G) :
    homogeneousPrism rho T U n f x =
      homogeneousValue rho n (schreierPrism rho T U n f) x := by
  let tuple : Fin n → G := fun i => (x i.castSucc)⁻¹ * x i.succ
  have hx : (fun i => x 0 * Fin.partialProd tuple i) = x :=
    Fin.partialProd_left_inv x
  change homogeneousPrism rho T U n f x = rho (x 0) (schreierPrism rho T U n f tuple)
  calc
    _ = homogeneousPrism rho T U n f (fun i => x 0 * Fin.partialProd tuple i) :=
      congrArg (homogeneousPrism rho T U n f) hx.symm
    _ = rho (x 0) (homogeneousPrism rho T U n f (Fin.partialProd tuple)) :=
      homogeneousPrism_mul rho T U n f (x 0) _
    _ = _ := congrArg (rho (x 0)) (homogeneousPrism_partialProd rho T U n f tuple)

private theorem prismAt_d (rho : Representation R G M) (T U : H.RightTransversal)
    (n : ℕ) (f : (Fin (n + 1) → H) → M) (t : (T : Set G))
    (x : Fin (n + 2) → G) :
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      prismAt rho T U n f t (x ∘ j.succAbove)) +
      prismAt rho T U (n + 1)
        (fun tuple => rho (tuple 0 : G) (f (Fin.tail tuple)) +
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) tuple)) t x =
    homogeneousValue (rho.comp H.subtype) (n + 1) f
        (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (x j)) -
      homogeneousValue (rho.comp H.subtype) (n + 1) f
        (fun j => T.schreierFactor t (x j)) := by
  let psi : Representation R H M := rho.comp H.subtype
  let df : (Fin (n + 2) → H) → M := fun tuple => rho (tuple 0 : G) (f (Fin.tail tuple)) +
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) tuple)
  let a : G → H := fun y => T.schreierFactor t y
  let b : G → H := fun y => T.changeFactor U t * U.schreierFactor (T.changeRep U t) y
  have h := SchreierPrism.homogeneous_prism_identity_succ a b n
    (homogeneousValue psi (n + 1) f) x
  have hd (i : Fin (n + 2)) :
      homogeneousValue psi (n + 2) df (SchreierPrism.vertices (a ∘ x) (b ∘ x) i) =
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
          homogeneousValue psi (n + 1) f
            (SchreierPrism.vertices (a ∘ x) (b ∘ x) i ∘ j.succAbove) :=
    (homogeneousValue_d psi (n + 1) f _).symm
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin (n + 2)) _ => congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (hd i))
  rw [← hs] at h
  exact h

private def homogeneousTrace (rho : Representation R G M) (T : H.RightTransversal)
    [H.FiniteIndex] (n : ℕ) (f : (Fin n → H) → M) (x : Fin (n + 1) → G) : M :=
  ∑ t : (T : Set G), rho (t : G)⁻¹
    (homogeneousValue (rho.comp H.subtype) n f (fun j => T.schreierFactor t (x j)))

private theorem homogeneousTrace_partialProd (rho : Representation R G M)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) (f : (Fin n → H) → M)
    (tuple : Fin n → G) :
    homogeneousTrace rho T n f (Fin.partialProd tuple) =
      ∑ t : (T : Set G), rho (t : G)⁻¹ (f (T.schreierFactorTuple t tuple)) := by
  unfold homogeneousTrace
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  unfold homogeneousValue
  have hzero : T.schreierFactor t (Fin.partialProd tuple 0) = 1 := by
    rw [Fin.partialProd_zero, T.schreierFactor_one]
  have hd : (fun i : Fin n =>
      (T.schreierFactor t (Fin.partialProd tuple i.castSucc))⁻¹ *
        T.schreierFactor t (Fin.partialProd tuple i.succ)) = T.schreierFactorTuple t tuple := by
    funext i
    exact T.schreierFactor_partialProd_difference t tuple i
  dsimp only
  rw [hzero, hd, map_one]
  rfl

private theorem homogeneousTrace_changeRep (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → H) → M) (x : Fin (n + 1) → G) :
    (∑ t : (T : Set G), rho (t : G)⁻¹
      (homogeneousValue (rho.comp H.subtype) n f
        (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (x j)))) =
      homogeneousTrace rho U n f x := by
  have ht (t : (T : Set G)) :
      rho (t : G)⁻¹ (homogeneousValue (rho.comp H.subtype) n f
        (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (x j))) =
      rho (T.changeRep U t : G)⁻¹
        (homogeneousValue (rho.comp H.subtype) n f
          (fun j => U.schreierFactor (T.changeRep U t) (x j))) := by
    rw [homogeneousValue_mul]
    change rho (t : G)⁻¹ (rho (T.changeFactor U t : G) _) = _
    rw [← Module.End.mul_apply, ← map_mul, T.inv_mul_changeFactor U]
  unfold homogeneousTrace
  calc
    _ = ∑ t : (T : Set G), rho (T.changeRep U t : G)⁻¹
        (homogeneousValue (rho.comp H.subtype) n f
          (fun j => U.schreierFactor (T.changeRep U t) (x j))) :=
      Finset.sum_congr rfl (fun t _ => ht t)
    _ = _ := (T.changeRepEquiv U).sum_comp
      (fun t : (U : Set G) => rho (t : G)⁻¹
        (homogeneousValue (rho.comp H.subtype) n f (fun j => U.schreierFactor t (x j))))

private theorem homogeneousPrism_d (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin (n + 1) → H) → M) (x : Fin (n + 2) → G) :
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      homogeneousPrism rho T U n f (x ∘ j.succAbove)) +
      homogeneousPrism rho T U (n + 1)
        (fun tuple => rho (tuple 0 : G) (f (Fin.tail tuple)) +
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) tuple)) x =
      homogeneousTrace rho U (n + 1) f x - homogeneousTrace rho T (n + 1) f x := by
  have ht (t : (T : Set G)) := congrArg (rho (t : G)⁻¹) (prismAt_d rho T U n f t x)
  have hall := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (t : (T : Set G)) _ => ht t)
  simp only [map_add, map_sub, map_sum, map_zsmul] at hall
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_comm] at hall
  calc
    _ = (∑ t : (T : Set G), rho (t : G)⁻¹
        (homogeneousValue (rho.comp H.subtype) (n + 1) f
          (fun j => T.changeFactor U t * U.schreierFactor (T.changeRep U t) (x j)))) -
      ∑ t : (T : Set G), rho (t : G)⁻¹
        (homogeneousValue (rho.comp H.subtype) (n + 1) f
          (fun j => T.schreierFactor t (x j))) := by
      simpa only [homogeneousPrism, Finset.smul_sum] using hall
    _ = _ := congrArg
      (fun z => z - homogeneousTrace rho T (n + 1) f x)
      (homogeneousTrace_changeRep rho T U (n + 1) f x)

/-- The actual finite Schreier prism satisfies delta K plus K delta in every positive degree. -/
theorem schreierPrism_identity_succ (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin (n + 1) → H) → M) (tuple : Fin (n + 1) → G) :
    rho (tuple 0) (schreierPrism rho T U n f (Fin.tail tuple)) +
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        schreierPrism rho T U n f (Fin.contractNth j (· * ·) tuple)) +
      schreierPrism rho T U (n + 1)
        (fun y => rho (y 0 : G) (f (Fin.tail y)) +
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) y)) tuple =
      (∑ u : (U : Set G), rho (u : G)⁻¹ (f (U.schreierFactorTuple u tuple))) -
        ∑ t : (T : Set G), rho (t : G)⁻¹ (f (T.schreierFactorTuple t tuple)) := by
  have h := homogeneousPrism_d rho T U n f (Fin.partialProd tuple)
  have hi (j : Fin (n + 2)) := homogeneousPrism_eq_homogeneousValue rho T U n f
    (Fin.partialProd tuple ∘ j.succAbove)
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (j : Fin (n + 2)) _ => congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z) (hi j))
  rw [hs, homogeneousValue_partialProd_d, homogeneousPrism_partialProd,
    homogeneousTrace_partialProd, homogeneousTrace_partialProd] at h
  exact h

/-- The actual zeroth Schreier prism accounts for the change of trace on every zero cochain. -/
theorem schreierPrism_identity_zero (rho : Representation R G M)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : (Fin 0 → H) → M) (tuple : Fin 0 → G) :
    schreierPrism rho T U 0
        (fun y => rho (y 0 : G) (f (Fin.tail y)) - f (Fin.tail y)) tuple =
      (∑ u : (U : Set G), rho (u : G)⁻¹ (f (U.schreierFactorTuple u tuple))) -
        ∑ t : (T : Set G), rho (t : G)⁻¹ (f (T.schreierFactorTuple t tuple)) := by
  let m : M := f (fun i => Fin.elim0 i)
  have hf (y : Fin 0 → H) : f y = m :=
    congrArg f (Subsingleton.elim y _)
  have hc (t : (T : Set G)) :
      T.schreierPrismTuple U t tuple (0 : Fin 1) 0 = T.changeFactor U t := by
    rw [T.schreierPrismTuple_inserted]
    change T.changeFactor U (T.schreierRepScan t tuple 0) = _
    rw [T.schreierRepScan_get_zero]
  rw [schreierPrism_apply]
  simp only [hf]
  have ht (t : (T : Set G)) :
      rho (t : G)⁻¹ (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) •
        (rho (T.schreierPrismTuple U t tuple i 0 : G) m - m)) =
          rho (T.changeRep U t : G)⁻¹ m - rho (t : G)⁻¹ m := by
    rw [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    rw [hc, map_sub, ← Module.End.mul_apply, ← map_mul, T.inv_mul_changeFactor U]
  calc
    _ = (∑ t : (T : Set G), rho (T.changeRep U t : G)⁻¹ m) -
        ∑ t : (T : Set G), rho (t : G)⁻¹ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun t _ => ht t)
    _ = _ := congrArg (fun z => z - ∑ t : (T : Set G), rho (t : G)⁻¹ m)
      ((T.changeRepEquiv U).sum_comp (fun u : (U : Set G) => rho (u : G)⁻¹ m))

end groupCohomology
