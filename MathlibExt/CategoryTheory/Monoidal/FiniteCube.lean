/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.OfSymmetric
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Preimage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Finite tensor cubes and their actual boundaries

The cube of a finite family of arrows is indexed by subsets of `Fin n`.
At a subset `S`, exactly the coordinates in `S` use the codomains; all
other coordinates use the domains. The maps tensor the original arrows
in newly added coordinates and identities in every unchanged coordinate.

The boundary is the colimit of the full cube with its terminal vertex
removed. Its inclusion into the terminal vertex retains every original
face map. The empty dimensional cube has the original tensor unit as
its tensor vertex and an initial boundary.

The alternating construction retains a separate coefficient before,
between, and after the varying letters. It has exactly `n + 1`
coefficient factors and degree zero is the original coefficient itself.
All tensors are the supplied binary monoidal tensor.

`boundaryPushoutIsColimit` proves that the full lower slice and the proper
upper slice form the actual boundary pushout. `tensorStepArrowIso` identifies
the complete attaching arrow with the original pushout product.
`alternatingPushoutProductIso` then identifies the literal alternating cube
arrow with the iterated products of the original letter arrows tensored
with every original coefficient in its original order. Degree one uses
the original arrow itself, and degree zero retains the original coefficient.

The cube and boundary constructions require only the stated ordinary
colimits. Tensor comparisons use preservation of their actual punctured
colimits; grouping coefficients additionally uses the actual braiding.
Filtration and monoid operations consume these constructions in subsequent modules.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.MonoidalCategory.FiniteCube

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

/-- The actual subset poset of the `n` original letter positions. -/
abbrev Index (n : ℕ) := Finset (Fin n)

/-- The proper faces, including the empty face whenever the dimension is positive. -/
abbrev Punctured (n : ℕ) := {S : Index n // S ≠ Finset.univ}

/-- The inclusion of all proper faces into the full original subset cube. -/
@[implicit_reducible]
def puncturedInclusion (n : ℕ) : Punctured n ⥤ Index n where
  obj S := S.1
  map f := homOfLE (leOfHom f)

/-- The empty dimensional cube has no proper face. -/
instance puncturedZeroIsEmpty : IsEmpty (Punctured 0) where
  false S := S.2 (Finset.ext fun i => i.elim0)

section IndexGeometry

variable {n : ℕ}

/-- Retain precisely the original nonfinal positions of a subset cube. -/
def «prefix» (S : Index (n + 1)) : Index n :=
  S.preimage Fin.castSucc (Set.injOn_of_injective (Fin.castSucc_injective n))

/-- Prefix membership is membership of the same original nonfinal position. -/
@[simp] theorem mem_prefix (S : Index (n + 1)) (i : Fin n) :
    i ∈ «prefix» S ↔ i.castSucc ∈ S := Finset.mem_preimage

/-- The prefix of the full original cube subset is the full preceding subset. -/
@[simp] theorem prefix_univ : «prefix» (Finset.univ : Index (n + 1)) = Finset.univ := by
  ext i
  simp only [mem_prefix, Finset.mem_univ]

/-- Include the original preceding subset without selecting the final coordinate. -/
def lower (S : Index n) : Index (n + 1) := S.map Fin.castSuccEmb

/-- Include the original preceding subset and select the final coordinate. -/
def upper (S : Index n) : Index (n + 1) := insert (Fin.last n) (lower S)

/-- Lower-face membership retains each original preceding coordinate. -/
@[simp] theorem mem_lower (S : Index n) (i : Fin n) : i.castSucc ∈ lower S ↔ i ∈ S :=
  Finset.mem_map' Fin.castSuccEmb

/-- The final coordinate is absent from every lower face. -/
@[simp] theorem notMem_last_lower (S : Index n) : Fin.last n ∉ lower S := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  exact Fin.castSucc_ne_last i hi

/-- Upper-face membership retains each original preceding coordinate. -/
@[simp] theorem mem_upper (S : Index n) (i : Fin n) : i.castSucc ∈ upper S ↔ i ∈ S := by
  simp only [upper, Finset.mem_insert, Fin.castSucc_ne_last, false_or, mem_lower]

/-- The final coordinate is present in every upper face. -/
@[simp] theorem mem_last_upper (S : Index n) : Fin.last n ∈ upper S := Finset.mem_insert_self _ _

/-- Prefixing the lower inclusion recovers the same original subset. -/
@[simp] theorem prefix_lower (S : Index n) : «prefix» (lower S) = S := by
  ext i
  simp only [mem_prefix, mem_lower]

/-- Prefixing the upper inclusion recovers the same original subset. -/
@[simp] theorem prefix_upper (S : Index n) : «prefix» (upper S) = S := by
  ext i
  simp only [mem_prefix, mem_upper]

/-- An unselected final coordinate reconstructs the original subset as a lower face. -/
theorem eq_lower_prefix (S : Index (n + 1)) (h : Fin.last n ∉ S) : S = lower («prefix» S) := by
  ext i
  cases i using Fin.lastCases with
  | last => simp only [h, notMem_last_lower]
  | cast i => simp only [mem_lower, mem_prefix]

/-- A selected final coordinate reconstructs the original subset as an upper face. -/
theorem eq_upper_prefix (S : Index (n + 1)) (h : Fin.last n ∈ S) : S = upper («prefix» S) := by
  ext i
  cases i using Fin.lastCases with
  | last => simp only [h, mem_last_upper]
  | cast i => simp only [mem_upper, mem_prefix]

/-- The full upper face is the full original cube subset. -/
@[simp] theorem upper_univ : upper (Finset.univ : Index n) = Finset.univ := by
  simpa only [prefix_univ] using (eq_upper_prefix Finset.univ (Finset.mem_univ (Fin.last n))).symm

/-- Every lower face is proper, regardless of its original preceding subset. -/
theorem lower_ne_univ (S : Index n) : lower S ≠ Finset.univ := by
  intro h
  exact notMem_last_lower S (h.symm ▸ Finset.mem_univ (Fin.last n))

/-- An upper face is proper exactly when its original preceding subset is proper. -/
@[simp] theorem upper_eq_univ_iff (S : Index n) : upper S = Finset.univ ↔ S = Finset.univ := by
  constructor
  · intro h
    simpa only [prefix_upper, prefix_univ] using congrArg «prefix» h
  · intro h
    rw [h, upper_univ]

/-- The prefix of a proper upper face is a proper original preceding subset. -/
theorem prefix_ne_univ (S : Punctured (n + 1)) (h : Fin.last n ∈ S.1) :
    «prefix» S.1 ≠ Finset.univ := by
  intro e
  apply S.2
  exact (eq_upper_prefix S.1 h).trans ((congrArg upper e).trans upper_univ)

/-- Lower inclusion preserves every original subset inclusion. -/
theorem lower_mono : Monotone (lower : Index n → Index (n + 1)) :=
  fun _ _ h => Finset.map_subset_map.mpr h

/-- Upper inclusion preserves every original subset inclusion. -/
theorem upper_mono : Monotone (upper : Index n → Index (n + 1)) := by
  intro S T h i hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · exact Finset.mem_insert.mpr (Or.inl hi)
  · exact Finset.mem_insert.mpr (Or.inr (lower_mono h hi))

/-- Prefixing preserves every original subset inclusion. -/
theorem prefix_mono : Monotone («prefix» : Index (n + 1) → Index n) := by
  intro S T h i hi
  exact (mem_prefix T i).mpr (h ((mem_prefix S i).mp hi))

/-- The actual functor retaining the original nonfinal positions of every cube face. -/
@[implicit_reducible]
def prefixFunctor (n : ℕ) : Index (n + 1) ⥤ Index n := (prefix_mono (n := n)).functor

/-- The original lower face includes into the corresponding original upper face. -/
theorem lower_subset_upper (S : Index n) : lower S ⊆ upper S := Finset.subset_insert _ _

/-- Every face includes into the upper face with its own original prefix. -/
theorem subset_upper_prefix (S : Index (n + 1)) : S ⊆ upper («prefix» S) := by
  intro i hi
  cases i using Fin.lastCases with
  | last => exact mem_last_upper _
  | cast i => exact (mem_upper _ i).mpr ((mem_prefix S i).mpr hi)

/-- A face without the final coordinate includes into the full original lower face. -/
theorem subset_lower_univ (S : Index (n + 1)) (h : Fin.last n ∉ S) : S ⊆ lower Finset.univ := by
  intro i hi
  cases i using Fin.lastCases with
  | last => exact (h hi).elim
  | cast i => exact (mem_lower _ i).mpr (Finset.mem_univ i)

/-- An original lower face includes into the lower prefix of every face containing it. -/
theorem subset_lower_prefix {S T : Index (n + 1)} (h : S ⊆ T) (hS : Fin.last n ∉ S) :
    S ⊆ lower («prefix» T) := by
  intro i hi
  cases i using Fin.lastCases with
  | last => exact (hS hi).elim
  | cast i => exact (mem_lower _ i).mpr ((mem_prefix T i).mpr (h hi))

/-- Lower inclusion retains the original number of selected preceding coordinates. -/
@[simp] theorem card_lower (S : Index n) : (lower S).card = S.card := Finset.card_map _

/-- Upper inclusion adds exactly the newly selected original final coordinate. -/
@[simp] theorem card_upper (S : Index n) : (upper S).card = S.card + 1 := by
  rw [upper, Finset.card_insert_of_notMem (notMem_last_lower S), card_lower]

/-- The original subset count splits into its unchanged prefix and its final coordinate. -/
theorem card_eq_prefix (S : Index (n + 1)) :
    S.card = («prefix» S).card + if Fin.last n ∈ S then 1 else 0 := by
  by_cases h : Fin.last n ∈ S
  · calc
      S.card = (upper («prefix» S)).card := congrArg Finset.card (eq_upper_prefix S h)
      _ = («prefix» S).card + if Fin.last n ∈ S then 1 else 0 := by rw [card_upper, ite_eq_left h]
  · calc
      S.card = (lower («prefix» S)).card := congrArg Finset.card (eq_lower_prefix S h)
      _ = («prefix» S).card + if Fin.last n ∈ S then 1 else 0 := by rw [card_lower,
        ite_eq_right h, Nat.add_zero]

/-- Every proper original face has strictly fewer selected coordinates than the full cube. -/
theorem card_lt (S : Punctured n) : S.1.card < n := by
  have h : S.1 ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, S.2⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card h

/-- The sole proper face of the original one dimensional cube. -/
@[implicit_reducible]
def puncturedOneEmpty : Punctured 1 :=
  ⟨∅, fun h => Finset.notMem_empty (0 : Fin 1) (h.symm ▸ Finset.mem_univ (0 : Fin 1))⟩

/-- Every proper face of a one dimensional cube is the original empty face. -/
theorem puncturedOne_eq_empty (S : Punctured 1) : S = puncturedOneEmpty :=
  Subtype.ext (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp (card_lt S)))

/-- The original empty face is terminal in the original punctured one dimensional cube. -/
def puncturedOneIsTerminal : IsTerminal puncturedOneEmpty :=
  IsTerminal.ofUniqueHom (fun S => eqToHom (puncturedOne_eq_empty S))
    (fun _ _ => Subsingleton.elim _ _)

end IndexGeometry

variable {C : Type u} [Category.{v} C]

section Family

variable {n : ℕ} (K L : Fin n → C)

/-- At a subset, retain the codomain in exactly the selected coordinates. -/
def vertexFamily (S : Index n) (i : Fin n) : C :=
  if i ∈ S then L i else K i

omit [Category.{v} C] in
/-- The terminal vertex has precisely the original codomain family. -/
@[simp] theorem vertexFamily_univ : vertexFamily K L Finset.univ = L := by
  funext i
  simp only [vertexFamily, Finset.mem_univ, ite_true]

omit [Category.{v} C] in
/-- The initial vertex has precisely the original domain family. -/
@[simp] theorem vertexFamily_empty : vertexFamily K L ∅ = K := by
  funext i
  simp only [vertexFamily, ite_eq_right (Finset.notMem_empty i)]

variable {K L}

/-- The original coordinate arrow for an inclusion of subsets. Newly added
coordinates use `f`; all unchanged coordinates use the original identity. -/
def familyMap (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⊆ T) (i : Fin n) :
    vertexFamily K L S i ⟶ vertexFamily K L T i :=
  if hi : i ∈ S then
    eqToHom (by simp only [vertexFamily, ite_eq_left hi, ite_eq_left (h hi)])
  else if hj : i ∈ T then
    eqToHom (by simp only [vertexFamily, ite_eq_right hi]) ≫ f i ≫
      eqToHom (by simp only [vertexFamily, ite_eq_left hj])
  else
    eqToHom (by simp only [vertexFamily, ite_eq_right hi, ite_eq_right hj])

/-- An already selected coordinate remains the original codomain identity. -/
theorem familyMap_selected (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⊆ T)
    (i : Fin n) (hi : i ∈ S) : HEq (familyMap f h i) (𝟙 (L i)) := by
  simp only [familyMap, dite_eq_left hi]
  have e : vertexFamily K L S i = L i := by simp only [vertexFamily, ite_eq_left hi]
  exact (eqToHom_heq_id_dom _ _ _).trans
    ((eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e))

/-- A newly selected coordinate is the actual original arrow. -/
theorem familyMap_added (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⊆ T)
    (i : Fin n) (hi : i ∉ S) (hj : i ∈ T) : HEq (familyMap f h i) (f i) := by
  simp only [familyMap, dite_eq_right hi, dite_eq_left hj, comp_eqToHom_heq_iff,
    eqToHom_comp_heq_iff]
  rfl

/-- An unselected coordinate remains the original domain identity. -/
theorem familyMap_unselected (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⊆ T)
    (i : Fin n) (hj : i ∉ T) : HEq (familyMap f h i) (𝟙 (K i)) := by
  have hi : i ∉ S := fun hi => hj (h hi)
  simp only [familyMap, dite_eq_right hi, dite_eq_right hj]
  have e : vertexFamily K L S i = K i := by simp only [vertexFamily, ite_eq_right hi]
  exact (eqToHom_heq_id_dom _ _ _).trans
    ((eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e))

/-- Coordinatewise maps of the original cube preserve identities. -/
@[simp] theorem familyMap_id (f : ∀ i, K i ⟶ L i) (S : Index n) :
    familyMap f (Finset.Subset.refl S) = fun i => 𝟙 (vertexFamily K L S i) := by
  funext i
  by_cases hi : i ∈ S
  · apply eq_of_heq
    have e : vertexFamily K L S i = L i := by simp only [vertexFamily, ite_eq_left hi]
    exact (familyMap_selected f _ i hi).trans
      ((eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e)).symm
  · apply eq_of_heq
    have e : vertexFamily K L S i = K i := by simp only [vertexFamily, ite_eq_right hi]
    exact (familyMap_unselected f _ i hi).trans
      ((eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e)).symm

/-- All face maps compose by composition of their original coordinate maps. -/
theorem familyMap_comp (f : ∀ i, K i ⟶ L i) {S T U : Index n}
    (h : S ⊆ T) (k : T ⊆ U) :
    (fun i => familyMap f h i ≫ familyMap f k i) = familyMap f (h.trans k) := by
  funext i
  by_cases hi : i ∈ S
  · have hj := h hi
    have hk := k hj
    apply eq_of_heq
    have eS : vertexFamily K L S i = L i := by simp only [vertexFamily, ite_eq_left hi]
    have eT : vertexFamily K L T i = L i := by simp only [vertexFamily, ite_eq_left hj]
    have eU : vertexFamily K L U i = L i := by simp only [vertexFamily, ite_eq_left hk]
    exact (heq_comp eS eT eU (familyMap_selected f h i hi) (familyMap_selected f k i hj)).trans
      ((heq_of_eq (Category.id_comp _)).trans (familyMap_selected f (h.trans k) i hi).symm)
  · by_cases hj : i ∈ T
    · have hk := k hj
      apply eq_of_heq
      have eS : vertexFamily K L S i = K i := by simp only [vertexFamily, ite_eq_right hi]
      have eT : vertexFamily K L T i = L i := by simp only [vertexFamily, ite_eq_left hj]
      have eU : vertexFamily K L U i = L i := by simp only [vertexFamily, ite_eq_left hk]
      exact (heq_comp eS eT eU (familyMap_added f h i hi hj) (familyMap_selected f k i hj)).trans
        ((heq_of_eq (Category.comp_id _)).trans (familyMap_added f (h.trans k) i hi hk).symm)
    · by_cases hk : i ∈ U
      · apply eq_of_heq
        have eS : vertexFamily K L S i = K i := by simp only [vertexFamily, ite_eq_right hi]
        have eT : vertexFamily K L T i = K i := by simp only [vertexFamily, ite_eq_right hj]
        have eU : vertexFamily K L U i = L i := by simp only [vertexFamily, ite_eq_left hk]
        exact (heq_comp eS eT eU (familyMap_unselected f h i hj) (familyMap_added f k i hj
          hk)).trans
          ((heq_of_eq (Category.id_comp _)).trans (familyMap_added f (h.trans k) i hi hk).symm)
      · apply eq_of_heq
        have eS : vertexFamily K L S i = K i := by simp only [vertexFamily, ite_eq_right hi]
        have eT : vertexFamily K L T i = K i := by simp only [vertexFamily, ite_eq_right hj]
        have eU : vertexFamily K L U i = K i := by simp only [vertexFamily, ite_eq_right hk]
        exact (heq_comp eS eT eU (familyMap_unselected f h i hj) (familyMap_unselected f k i
          hk)).trans
          ((heq_of_eq (Category.id_comp _)).trans (familyMap_unselected f (h.trans k) i hk).symm)

/-- The original subset cube of finite object families, before tensoring. -/
def familyCube (f : ∀ i, K i ⟶ L i) : Index n ⥤ (Fin n → C) where
  obj := vertexFamily K L
  map h := familyMap f (leOfHom h)
  map_id S := familyMap_id f S
  map_comp h k := (familyMap_comp f (leOfHom h) (leOfHom k)).symm

/-- The original face map in one coordinate is independent of the other original coordinate
objects. -/
theorem familyMap_coordinate (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⊆ T) (i : Fin n) :
    HEq (familyMap f h i) (familyMap (fun _ : Fin n => f i) h i) := by
  by_cases hS : i ∈ S
  · exact (familyMap_selected f h i hS).trans
      (familyMap_selected (fun _ : Fin n => f i) h i hS).symm
  · by_cases hT : i ∈ T
    · exact (familyMap_added f h i hS hT).trans
        (familyMap_added (fun _ : Fin n => f i) h i hS hT).symm
    · exact (familyMap_unselected f h i hT).trans
        (familyMap_unselected (fun _ : Fin n => f i) h i hT).symm

/-- The original arrow cube restricted to one original coordinate. -/
@[implicit_reducible]
def coordinateCube {K L : C} (f : K ⟶ L) (i : Fin n) : Index n ⥤ C :=
  familyCube (fun _ : Fin n => f) ⋙ Pi.eval (fun _ : Fin n => C) i

end Family

section PrefixFamily

variable {n : ℕ} {K L : Fin (n + 1) → C}

omit [Category.{v} C] in
/-- The prefix vertex retains exactly the original nonfinal tensor inputs. -/
theorem vertexFamily_prefix (S : Index (n + 1)) :
    (fun i : Fin n => vertexFamily K L S i.castSucc) =
      vertexFamily (fun i => K i.castSucc) (fun i => L i.castSucc) («prefix» S) := by
  funext i
  simp only [vertexFamily, mem_prefix]

/-- Every original face inclusion retains its original map in every nonfinal tensor input. -/
theorem familyMap_prefix (f : ∀ i, K i ⟶ L i) {S T : Index (n + 1)} (h : S ⊆ T) (i : Fin n) :
    HEq (familyMap f h i.castSucc)
      (familyMap (fun j : Fin n => f j.castSucc) (prefix_mono h) i) := by
  have hp : «prefix» S ⊆ «prefix» T := prefix_mono h
  change HEq (familyMap f h i.castSucc) (familyMap (fun j : Fin n => f j.castSucc) hp i)
  by_cases hS : i.castSucc ∈ S
  · exact (familyMap_selected f h i.castSucc hS).trans
      (familyMap_selected (fun j : Fin n => f j.castSucc) hp i ((mem_prefix S i).mpr hS)).symm
  · by_cases hT : i.castSucc ∈ T
    · exact (familyMap_added f h i.castSucc hS hT).trans
        (familyMap_added (fun j : Fin n => f j.castSucc) hp i
          (fun e => hS ((mem_prefix S i).mp e)) ((mem_prefix T i).mpr hT)).symm
    · exact (familyMap_unselected f h i.castSucc hT).trans
        (familyMap_unselected (fun j : Fin n => f j.castSucc) hp i
          (fun e => hT ((mem_prefix T i).mp e))).symm

end PrefixFamily

section Tensor

variable [MonoidalCategory C] {n : ℕ} {K L : Fin n → C}

/-- Tensor the original finite family cube using the canonical ordered
heterogeneous tensor functor. -/
def tensorCube (f : ∀ i, K i ⟶ L i) : Index n ⥤ C :=
  familyCube f ⋙ OrderedTensor.functor C n

/-- Every tensor vertex is the literal finite tensor of its original coordinates. -/
@[simp] theorem tensorCube_obj (f : ∀ i, K i ⟶ L i) (S : Index n) :
    (tensorCube f).obj S = OrderedTensor.obj (vertexFamily K L S) := rfl

/-- Every tensor face map is the tensor of its actual coordinate face maps. -/
@[simp] theorem tensorCube_map (f : ∀ i, K i ⟶ L i) {S T : Index n} (h : S ⟶ T) :
    (tensorCube f).map h = OrderedTensor.map (familyMap f (leOfHom h)) := rfl

/-- The terminal tensor vertex is the tensor of the original codomains. -/
theorem tensorCube_obj_univ (f : ∀ i, K i ⟶ L i) :
    (tensorCube f).obj Finset.univ = OrderedTensor.obj L := by
  rw [tensorCube_obj, vertexFamily_univ]

/-- The initial tensor vertex is the tensor of the original domains. -/
theorem tensorCube_obj_empty (f : ∀ i, K i ⟶ L i) :
    (tensorCube f).obj ∅ = OrderedTensor.obj K := by
  rw [tensorCube_obj, vertexFamily_empty]

/-- A zero dimensional tensor cube has exactly the original tensor unit. -/
@[simp] theorem tensorCube_obj_zero {K L : Fin 0 → C} (f : ∀ i, K i ⟶ L i)
    (S : Index 0) : (tensorCube f).obj S = 𝟙_ C := rfl

/-- The literal alternating tensor, retaining all original coefficient factors. -/
def alternatingObj : {n : ℕ} → (Fin (n + 1) → C) → (Fin n → C) → C
  | 0, A, _ => A 0
  | n + 1, A, X =>
      (alternatingObj (fun i : Fin (n + 1) => A i.castSucc)
        (fun i : Fin n => X i.castSucc) ⊗ X (Fin.last n)) ⊗ A (Fin.last (n + 1))

/-- Tensor the actual maps in every coefficient and letter position of a word. -/
def alternatingMap : {n : ℕ} → {A B : Fin (n + 1) → C} → {X Y : Fin n → C} →
    (∀ i, A i ⟶ B i) → (∀ i, X i ⟶ Y i) → (alternatingObj A X ⟶ alternatingObj B Y)
  | 0, _, _, _, _, a, _ => a 0
  | n + 1, _, _, _, _, a, f =>
      (alternatingMap (fun i : Fin (n + 1) => a i.castSucc)
        (fun i : Fin n => f i.castSucc) ⊗ₘ f (Fin.last n)) ⊗ₘ a (Fin.last (n + 1))

/-- The word with no letters is precisely the original coefficient. -/
@[simp] theorem alternatingObj_zero (A : Fin 1 → C) (X : Fin 0 → C) :
    alternatingObj A X = A 0 := rfl

/-- The successor word adds one original letter followed by one original coefficient. -/
@[simp] theorem alternatingObj_succ (A : Fin (n + 2) → C) (X : Fin (n + 1) → C) :
    alternatingObj A X =
      (alternatingObj (fun i : Fin (n + 1) => A i.castSucc)
        (fun i : Fin n => X i.castSucc) ⊗ X (Fin.last n)) ⊗ A (Fin.last (n + 1)) := rfl

/-- Alternating component maps preserve the original identities. -/
@[simp] theorem alternatingMap_id : ∀ {n : ℕ} (A : Fin (n + 1) → C) (X : Fin n → C),
    alternatingMap (fun i => 𝟙 (A i)) (fun i => 𝟙 (X i)) = 𝟙 (alternatingObj A X)
  | 0, _, _ => rfl
  | n + 1, A, X => by
      change (alternatingMap (fun i : Fin (n + 1) => 𝟙 (A i.castSucc))
        (fun i : Fin n => 𝟙 (X i.castSucc)) ⊗ₘ 𝟙 (X (Fin.last n))) ⊗ₘ
        𝟙 (A (Fin.last (n + 1))) = _
      rw [alternatingMap_id, id_tensorHom_id, id_tensorHom_id]
      rfl

/-- Alternating component maps compose in every original position. -/
theorem alternatingMap_comp : ∀ {n : ℕ} {A B D : Fin (n + 1) → C} {X Y Z : Fin n → C}
    (a : ∀ i, A i ⟶ B i) (b : ∀ i, B i ⟶ D i)
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i),
    alternatingMap (fun i => a i ≫ b i) (fun i => f i ≫ g i) =
      alternatingMap a f ≫ alternatingMap b g
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, A, B, D, X, Y, Z, a, b, f, g => by
      change (alternatingMap (fun i : Fin (n + 1) => a i.castSucc ≫ b i.castSucc)
        (fun i : Fin n => f i.castSucc ≫ g i.castSucc) ⊗ₘ
          (f (Fin.last n) ≫ g (Fin.last n))) ⊗ₘ
          (a (Fin.last (n + 1)) ≫ b (Fin.last (n + 1))) = _
      rw [alternatingMap_comp, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
      rfl

/-- Equal original coefficient and letter inputs transport their actual alternating
component maps. -/
theorem alternatingMap_heq {A A' B B' : Fin (n + 1) → C} {X X' Y Y' : Fin n → C}
    (hA : ∀ i, A i = A' i) (hB : ∀ i, B i = B' i)
    (hX : ∀ i, X i = X' i) (hY : ∀ i, Y i = Y' i)
    (a : ∀ i, A i ⟶ B i) (a' : ∀ i, A' i ⟶ B' i)
    (f : ∀ i, X i ⟶ Y i) (f' : ∀ i, X' i ⟶ Y' i)
    (ha : ∀ i, HEq (a i) (a' i)) (hf : ∀ i, HEq (f i) (f' i)) :
    HEq (alternatingMap a f) (alternatingMap a' f') := by
  have eA : A = A' := funext hA
  have eB : B = B' := funext hB
  have eX : X = X' := funext hX
  have eY : Y = Y' := funext hY
  subst A'
  subst B'
  subst X'
  subst Y'
  have ea : a = a' := funext (fun i => eq_of_heq (ha i))
  have ef : f = f' := funext (fun i => eq_of_heq (hf i))
  subst a'
  subst f'
  rfl

/-- The alternating word functor varies the original letters, with all
original coefficient maps equal to identities. -/
def alternatingFunctor (A : Fin (n + 1) → C) : (Fin n → C) ⥤ C where
  obj X := alternatingObj A X
  map f := alternatingMap (fun i => 𝟙 (A i)) f
  map_id X := alternatingMap_id A X
  map_comp f g := by
    change alternatingMap (fun i => 𝟙 (A i)) (fun i => f i ≫ g i) =
      alternatingMap (fun i => 𝟙 (A i)) f ≫ alternatingMap (fun i => 𝟙 (A i)) g
    simpa only [Category.id_comp] using
      alternatingMap_comp (fun i => 𝟙 (A i)) (fun i => 𝟙 (A i)) f g

/-- The literal subset word cube with an arbitrary original coefficient
before, between, and after its varying letters. -/
def alternatingCube (A : Fin (n + 1) → C) (f : ∀ i, K i ⟶ L i) : Index n ⥤ C :=
  familyCube f ⋙ alternatingFunctor A

/-- Read back the literal word at every original subset. -/
@[simp] theorem alternatingCube_obj (A : Fin (n + 1) → C) (f : ∀ i, K i ⟶ L i)
    (S : Index n) : (alternatingCube A f).obj S = alternatingObj A (vertexFamily K L S) := rfl

/-- Read back every original word face as its actual alternating tensor map. -/
@[simp] theorem alternatingCube_map (A : Fin (n + 1) → C) (f : ∀ i, K i ⟶ L i)
    {S T : Index n} (h : S ⟶ T) :
    (alternatingCube A f).map h = alternatingMap (fun i => 𝟙 (A i)) (familyMap f (leOfHom h)) := rfl

/-- The full word contains exactly the original codomain letters and coefficients. -/
theorem alternatingCube_obj_univ (A : Fin (n + 1) → C) (f : ∀ i, K i ⟶ L i) :
    (alternatingCube A f).obj Finset.univ = alternatingObj A L := by
  rw [alternatingCube_obj, vertexFamily_univ]

/-- The empty subset word contains exactly the original domain letters and coefficients. -/
theorem alternatingCube_obj_empty (A : Fin (n + 1) → C) (f : ∀ i, K i ⟶ L i) :
    (alternatingCube A f).obj ∅ = alternatingObj A K := by
  rw [alternatingCube_obj, vertexFamily_empty]

/-- A zero letter word cube has the original coefficient as its only vertex. -/
@[simp] theorem alternatingCube_obj_zero (A : Fin 1 → C) {K L : Fin 0 → C}
    (f : ∀ i, K i ⟶ L i) (S : Index 0) : (alternatingCube A f).obj S = A 0 := rfl

/-- Add one original arrow as the final tensor coordinate of an arbitrary original cube. -/
@[implicit_reducible]
def tensorStep (F : Index n ⥤ C) {K L : C} (f : K ⟶ L) : Index (n + 1) ⥤ C :=
  ((prefixFunctor n ⋙ F).prod' (coordinateCube f (Fin.last n))) ⋙ tensor C

/-- The step vertex is the original prefix vertex tensored with the actual final coordinate. -/
@[simp] theorem tensorStep_obj (F : Index n ⥤ C) {K L : C} (f : K ⟶ L) (S : Index (n + 1)) :
    (tensorStep F f).obj S = F.obj («prefix» S) ⊗ if Fin.last n ∈ S then L else K := rfl

/-- The step face tensors the original prefix face with the actual final-coordinate face. -/
@[simp] theorem tensorStep_map (F : Index n ⥤ C) {K L : C} (f : K ⟶ L)
    {S T : Index (n + 1)} (h : S ⟶ T) :
    (tensorStep F f).map h =
      F.map ((prefixFunctor n).map h) ⊗ₘ (coordinateCube f (Fin.last n)).map h := rfl

end Tensor

section TensorRecursion

variable [MonoidalCategory C] {n : ℕ} {K L : Fin (n + 1) → C}

/-- The full original finite tensor cube is the tensor step of its original preceding cube
and final arrow. -/
def tensorCubeStepIso (f : ∀ i, K i ⟶ L i) :
    tensorCube f ≅ tensorStep (tensorCube (fun i : Fin n => f i.castSucc)) (f (Fin.last n)) := by
  refine eqToIso (Functor.hext ?_ ?_)
  · intro S
    change OrderedTensor.obj (vertexFamily K L S) =
      OrderedTensor.obj (vertexFamily (fun i => K i.castSucc) (fun i =>
        L i.castSucc) («prefix» S)) ⊗
        (coordinateCube (f (Fin.last n)) (Fin.last n)).obj S
    rw [OrderedTensor.obj_succ, vertexFamily_prefix]
    rfl
  · intro S T h
    change HEq (OrderedTensor.map (familyMap f (leOfHom h)))
      (OrderedTensor.map (familyMap (fun i : Fin n => f i.castSucc) (prefix_mono (leOfHom h))) ⊗ₘ
        familyMap (fun _ : Fin (n + 1) => f (Fin.last n)) (leOfHom h) (Fin.last n))
    exact OrderedTensor.map_succ_heq (vertexFamily_prefix S) (vertexFamily_prefix T) rfl rfl
      (familyMap f (leOfHom h))
      (familyMap (fun i : Fin n => f i.castSucc) (prefix_mono (leOfHom h)))
      (familyMap (fun _ : Fin (n + 1) => f (Fin.last n)) (leOfHom h) (Fin.last n))
      (familyMap_prefix f (leOfHom h)) (familyMap_coordinate f (leOfHom h) (Fin.last n))

/-- The full original alternating word cube is its original preceding word cube,
the original final letter arrow, and the original final coefficient tensor factor. -/
def alternatingCubeStepIso (A : Fin (n + 2) → C) (f : ∀ i, K i ⟶ L i) :
    alternatingCube A f ≅
      tensorStep (alternatingCube (fun i : Fin (n + 1) => A i.castSucc)
        (fun i : Fin n => f i.castSucc)) (f (Fin.last n)) ⋙ tensorRight (A (Fin.last (n + 1))) := by
  refine eqToIso (Functor.hext ?_ ?_)
  · intro S
    change (alternatingObj (fun i : Fin (n + 1) => A i.castSucc)
        (fun i : Fin n => vertexFamily K L S i.castSucc) ⊗ vertexFamily K L S (Fin.last n)) ⊗
        A (Fin.last (n + 1)) =
      (alternatingObj (fun i : Fin (n + 1) => A i.castSucc)
        (vertexFamily (fun i => K i.castSucc) (fun i => L i.castSucc) («prefix» S)) ⊗
          (coordinateCube (f (Fin.last n)) (Fin.last n)).obj S) ⊗ A (Fin.last (n + 1))
    rw [vertexFamily_prefix]
    rfl
  · intro S T h
    let a : Fin (n + 1) → C := fun i => A i.castSucc
    have hs := vertexFamily_prefix (K := K) (L := L) S
    have ht := vertexFamily_prefix (K := K) (L := L) T
    have hm := alternatingMap_heq (fun _ => rfl) (fun _ => rfl) (congrFun hs) (congrFun ht)
      (fun i : Fin (n + 1) => 𝟙 (a i)) (fun i : Fin (n + 1) => 𝟙 (a i))
      (fun i : Fin n => familyMap f (leOfHom h) i.castSucc)
      (familyMap (fun i : Fin n => f i.castSucc) (prefix_mono (leOfHom h)))
      (fun _ => HEq.rfl) (familyMap_prefix f (leOfHom h))
    have hb := OrderedTensor.tensorHom_heq (congrArg (alternatingObj a) hs)
      (congrArg (alternatingObj a) ht) rfl rfl
      (alternatingMap (fun i : Fin (n + 1) => 𝟙 (a i))
        (fun i : Fin n => familyMap f (leOfHom h) i.castSucc))
      (familyMap f (leOfHom h) (Fin.last n))
      (alternatingMap (fun i : Fin (n + 1) => 𝟙 (a i))
        (familyMap (fun i : Fin n => f i.castSucc) (prefix_mono (leOfHom h))))
      (familyMap (fun _ : Fin (n + 1) => f (Fin.last n)) (leOfHom h) (Fin.last n))
      hm (familyMap_coordinate f (leOfHom h) (Fin.last n))
    change HEq
      (((alternatingMap (fun i : Fin (n + 1) => 𝟙 (a i))
        (fun i : Fin n => familyMap f (leOfHom h) i.castSucc)) ⊗ₘ
          familyMap f (leOfHom h) (Fin.last n)) ⊗ₘ 𝟙 (A (Fin.last (n + 1))))
      ((alternatingMap (fun i : Fin (n + 1) => 𝟙 (a i))
        (familyMap (fun i : Fin n => f i.castSucc) (prefix_mono (leOfHom h))) ⊗ₘ
          familyMap (fun _ : Fin (n + 1) => f (Fin.last n)) (leOfHom h) (Fin.last n)) ▷
            A (Fin.last (n + 1)))
    rw [← tensorHom_id]
    exact OrderedTensor.tensorHom_heq
      (congrArg (fun X => X ⊗ vertexFamily K L S (Fin.last n)) (congrArg (alternatingObj a) hs))
      (congrArg (fun X => X ⊗ vertexFamily K L T (Fin.last n)) (congrArg (alternatingObj a) ht))
      rfl rfl _ _ _ _ hb HEq.rfl

end TensorRecursion

section Boundary

variable {n : ℕ} (F : Index n ⥤ C)

/-- The original cube restricted to all its proper faces. -/
abbrev punctured : Punctured n ⥤ C := puncturedInclusion n ⋙ F

/-- Every proper face maps to the original terminal cube vertex. -/
def topCocone : Cocone (punctured F) where
  pt := F.obj Finset.univ
  ι :=
    { app S := F.map (homOfLE (Finset.subset_univ S.1))
      naturality S T h := by
        dsimp only [punctured, puncturedInclusion, Functor.comp_map, Functor.const_obj_map]
        rw [← F.map_comp]
        simpa only [homOfLE_comp] using
          (Category.comp_id (F.map (homOfLE (Finset.subset_univ S.1)))).symm }

variable [HasColimit (punctured F)]

/-- The actual colimit of the punctured original cube. -/
abbrev boundary : C := colimit (punctured F)

/-- The original leg from one proper face into the punctured cube colimit. -/
def boundaryι (S : Punctured n) : F.obj S.1 ⟶ boundary F := colimit.ι (punctured F) S

/-- The actual attaching arrow from the punctured cube to its terminal vertex. -/
def boundaryToTop : boundary F ⟶ F.obj Finset.univ := colimit.desc (punctured F) (topCocone F)

/-- Every original face leg of the attaching map is its original cube map. -/
@[reassoc (attr := simp)] theorem boundaryι_boundaryToTop (S : Punctured n) :
    boundaryι F S ≫ boundaryToTop F = F.map (homOfLE (Finset.subset_univ S.1)) :=
  colimit.ι_desc (topCocone F) S

/-- The original punctured cube legs are compatible along every proper-face inclusion. -/
@[reassoc (attr := simp)] theorem boundaryι_naturality {S T : Punctured n} (h : S ⟶ T) :
    F.map (homOfLE (leOfHom h)) ≫ boundaryι F T = boundaryι F S :=
  colimit.w (punctured F) h

/-- Morphisms from the boundary are determined by all original proper faces. -/
@[ext] theorem boundary_hom_ext {Z : C} {f g : boundary F ⟶ Z}
    (h : ∀ S, boundaryι F S ≫ f = boundaryι F S ≫ g) : f = g := colimit.hom_ext h

/-- Descend a compatible actual cocone on the original proper faces. -/
def boundaryDesc (c : Cocone (punctured F)) : boundary F ⟶ c.pt := colimit.desc (punctured F) c

/-- Every original proper face evaluates to the supplied original cocone leg. -/
@[reassoc (attr := simp)] theorem boundaryι_desc (c : Cocone (punctured F)) (S : Punctured n) :
    boundaryι F S ≫ boundaryDesc F c = c.ι.app S := colimit.ι_desc c S

/-- The original boundary cocone is a colimit; no boundary carrier is an input. -/
def boundaryIsColimit : IsColimit (colimit.cocone (punctured F)) := colimit.isColimit (punctured F)

variable {F} {G : Index n ⥤ C} [HasColimit (punctured G)]

/-- Map actual punctured cube colimits by the original map of full cubes. -/
def boundaryMap (η : F ⟶ G) : boundary F ⟶ boundary G :=
  colimMap (Functor.whiskerLeft (puncturedInclusion n) η)

/-- Original face legs retain the original component of a map of cubes. -/
@[reassoc (attr := simp)] theorem boundaryι_map (η : F ⟶ G) (S : Punctured n) :
    boundaryι F S ≫ boundaryMap η = η.app S.1 ≫ boundaryι G S :=
  ι_colimMap (Functor.whiskerLeft (puncturedInclusion n) η) S

/-- The boundary-to-top arrows are natural in the full original cube. -/
@[reassoc] theorem boundaryToTop_naturality (η : F ⟶ G) :
    boundaryToTop F ≫ η.app Finset.univ = boundaryMap η ≫ boundaryToTop G := by
  apply boundary_hom_ext F
  intro S
  simp only [boundaryι_boundaryToTop_assoc, boundaryι_map_assoc,
    boundaryι_boundaryToTop]
  exact η.naturality (homOfLE (Finset.subset_univ S.1))

end Boundary

section BoundaryFunctoriality

variable {n : ℕ} {F G : Index n ⥤ C}
variable [HasColimit (punctured F)] [HasColimit (punctured G)]

/-- An original isomorphism of full cubes identifies their actual punctured colimits. -/
def boundaryIso (e : F ≅ G) : boundary F ≅ boundary G :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (puncturedInclusion n) e)

/-- The boundary isomorphism preserves each original face and its original comparison map. -/
@[reassoc (attr := simp)] theorem boundaryι_iso (e : F ≅ G) (S : Punctured n) :
    boundaryι F S ≫ (boundaryIso e).hom = e.hom.app S.1 ≫ boundaryι G S :=
  HasColimit.ι_isoOfNatIso_hom (Functor.isoWhiskerLeft (puncturedInclusion n) e) S

/-- The attaching arrows retain the whole original cube isomorphism,
on both their actual source colimits and their terminal vertices. -/
def boundaryArrowIso (e : F ≅ G) : Arrow.mk (boundaryToTop F) ≅ Arrow.mk (boundaryToTop G) :=
  Arrow.isoMk (boundaryIso e) (e.app Finset.univ) (by
    change (boundaryIso e).hom ≫ boundaryToTop G = boundaryToTop F ≫ e.hom.app Finset.univ
    apply boundary_hom_ext F
    intro S
    rw [← Category.assoc, boundaryι_iso, Category.assoc, boundaryι_boundaryToTop,
      ← Category.assoc, boundaryι_boundaryToTop]
    exact (e.hom.naturality (homOfLE (Finset.subset_univ S.1))).symm)

end BoundaryFunctoriality

section BoundaryPreservation

universe v' u'

variable {D : Type u'} [Category.{v'} D] {n : ℕ} (F : Index n ⥤ C) (G : C ⥤ D)
variable [HasColimit (punctured F)] [PreservesColimit (punctured F) G]
variable [HasColimit (punctured (F ⋙ G))]

/-- Separate tensor preservation, or any supplied preservation of the actual
punctured cube, identifies its new boundary with the image of its original boundary. -/
def boundaryPostIso : boundary (F ⋙ G) ≅ G.obj (boundary F) :=
  (preservesColimitIso G (punctured F)).symm

/-- Every original proper face is retained by the preserved boundary comparison. -/
@[reassoc (attr := simp)] theorem boundaryι_postIso (S : Punctured n) :
    boundaryι (F ⋙ G) S ≫ (boundaryPostIso F G).hom = G.map (boundaryι F S) :=
  ι_preservesColimitIso_inv G (punctured F) S

/-- The preserved boundary comparison retains the original full attaching map. -/
@[reassoc] theorem boundaryPostIso_toTop :
    (boundaryPostIso F G).hom ≫ G.map (boundaryToTop F) = boundaryToTop (F ⋙ G) := by
  apply boundary_hom_ext (F ⋙ G)
  intro S
  rw [← Category.assoc, boundaryι_postIso, ← G.map_comp, boundaryι_boundaryToTop,
    boundaryι_boundaryToTop]
  rfl

/-- A preserved punctured cube identifies the entire attaching arrow with the
image of its original attaching arrow, including both source and target maps. -/
def boundaryPostArrowIso :
    Arrow.mk (boundaryToTop (F ⋙ G)) ≅ G.mapArrow.obj (Arrow.mk (boundaryToTop F)) :=
  Arrow.isoMk (boundaryPostIso F G) (Iso.refl (G.obj (F.obj Finset.univ))) (by
    change (boundaryPostIso F G).hom ≫ G.map (boundaryToTop F) =
      boundaryToTop (F ⋙ G) ≫ 𝟙 (G.obj (F.obj Finset.univ))
    exact (boundaryPostIso_toTop F G).trans
      (Category.comp_id (boundaryToTop (F ⋙ G))).symm)

end BoundaryPreservation

section Slices

variable {n : ℕ}

/-- The full original lower slice inclusion. -/
@[implicit_reducible]
def lowerFunctor (n : ℕ) : Index n ⥤ Index (n + 1) := (lower_mono (n := n)).functor

/-- The full original upper slice inclusion. -/
@[implicit_reducible]
def upperFunctor (n : ℕ) : Index n ⥤ Index (n + 1) := (upper_mono (n := n)).functor

/-- Every lower slice vertex is an actual proper face of the full cube. -/
@[implicit_reducible]
def lowerPunctured (n : ℕ) : Index n ⥤ Punctured (n + 1) where
  obj S := ⟨lower S, lower_ne_univ S⟩
  map h := homOfLE (lower_mono (leOfHom h))

/-- Every proper upper slice vertex is an actual proper face of the full cube. -/
@[implicit_reducible]
def upperPunctured (n : ℕ) : Punctured n ⥤ Punctured (n + 1) where
  obj S := ⟨upper S.1, fun h => S.2 ((upper_eq_univ_iff S.1).mp h)⟩
  map h := homOfLE (upper_mono (leOfHom h))

variable (F : Index (n + 1) ⥤ C)

/-- The original full lower slice of a cube. -/
abbrev lowerCube : Index n ⥤ C := lowerFunctor n ⋙ F

/-- The original full upper slice of a cube. -/
abbrev upperCube : Index n ⥤ C := upperFunctor n ⋙ F

/-- Every vertical face of the original cube, simultaneously for all preceding subsets. -/
def verticalFaces : lowerCube F ⟶ upperCube F where
  app S := F.map (homOfLE (lower_subset_upper S))
  naturality S T h := by
    dsimp only [lowerCube, upperCube, lowerFunctor, upperFunctor, Monotone.functor,
      Functor.comp_map]
    rw [← F.map_comp, ← F.map_comp]
    congr 1

variable [HasColimit (punctured F)]

/-- The original full lower-slice terminal vertex includes into the actual cube boundary. -/
@[implicit_reducible]
def lowerTopInclusion : F.obj (lower Finset.univ) ⟶ boundary F :=
  boundaryι F ((lowerPunctured n).obj Finset.univ)

/-- The original proper upper faces form an actual cocone in the full cube boundary. -/
def upperBoundaryCocone : Cocone (punctured (upperCube F)) where
  pt := boundary F
  ι :=
    { app S := boundaryι F ((upperPunctured n).obj S)
      naturality S T h := by
        change F.map (homOfLE (upper_mono (leOfHom h))) ≫
            boundaryι F ((upperPunctured n).obj T) =
          boundaryι F ((upperPunctured n).obj S) ≫ 𝟙 (boundary F)
        rw [Category.comp_id]
        exact boundaryι_naturality F ((upperPunctured n).map h) }

variable [HasColimit (punctured (upperCube F))]

/-- The actual upper-slice boundary maps to the full cube boundary by all its original legs. -/
@[implicit_reducible]
def upperBoundaryInclusion : boundary (upperCube F) ⟶ boundary F :=
  boundaryDesc (upperCube F) (upperBoundaryCocone F)

/-- Every original upper-face leg is preserved by its actual boundary inclusion. -/
@[reassoc (attr := simp)] theorem boundaryι_upperBoundaryInclusion (S : Punctured n) :
    boundaryι (upperCube F) S ≫ upperBoundaryInclusion F = boundaryι F ((upperPunctured n).obj S) :=
  boundaryι_desc (upperCube F) (upperBoundaryCocone F) S

variable [HasColimit (punctured (lowerCube F))]

/-- All original lower-boundary legs agree on the lower-top and upper-boundary routes. -/
@[reassoc] theorem boundarySlices_condition :
    boundaryToTop (lowerCube F) ≫ lowerTopInclusion F =
      boundaryMap (verticalFaces F) ≫ upperBoundaryInclusion F := by
  apply boundary_hom_ext (lowerCube F)
  intro S
  rw [← Category.assoc, boundaryι_boundaryToTop, ← Category.assoc, boundaryι_map,
    Category.assoc, boundaryι_upperBoundaryInclusion]
  change F.map (homOfLE (lower_mono (Finset.subset_univ S.1))) ≫
      boundaryι F ((lowerPunctured n).obj Finset.univ) =
    F.map (homOfLE (lower_subset_upper S.1)) ≫ boundaryι F ((upperPunctured n).obj S)
  exact (boundaryι_naturality F ((lowerPunctured n).map (homOfLE (Finset.subset_univ S.1)))).trans
    (boundaryι_naturality F (homOfLE (lower_subset_upper S.1) :
      (lowerPunctured n).obj S.1 ⟶ (upperPunctured n).obj S)).symm

/-- The actual square expressing the full cube boundary as a union of its two original slices. -/
@[implicit_reducible]
def boundaryPushoutCocone :
    PushoutCocone (boundaryToTop (lowerCube F)) (boundaryMap (verticalFaces F)) :=
  PushoutCocone.mk (lowerTopInclusion F) (upperBoundaryInclusion F) (boundarySlices_condition F)

end Slices

section TensorSlices

variable {n : ℕ}

/-- Restricting the original lower inclusion to its preceding coordinates is the identity. -/
def prefixLowerIso (n : ℕ) : lowerFunctor n ⋙ prefixFunctor n ≅ 𝟭 (Index n) :=
  eqToIso (Functor.ext (fun S => prefix_lower S) (fun _ _ _ => Subsingleton.elim _ _))

/-- Restricting the original upper inclusion to its preceding coordinates is the identity. -/
def prefixUpperIso (n : ℕ) : upperFunctor n ⋙ prefixFunctor n ≅ 𝟭 (Index n) :=
  eqToIso (Functor.ext (fun S => prefix_upper S) (fun _ _ _ => Subsingleton.elim _ _))

/-- The original final-coordinate arrow is constant at its domain on the full lower slice. -/
def coordinateLowerIso {K L : C} (f : K ⟶ L) :
    lowerFunctor n ⋙ coordinateCube f (Fin.last n) ≅ (Functor.const (Index n)).obj K := by
  refine eqToIso (Functor.hext ?_ ?_)
  · intro S
    change (if Fin.last n ∈ lower S then L else K) = K
    exact ite_eq_right (notMem_last_lower S)
  · intro S T h
    change HEq (familyMap (fun _ : Fin (n + 1) => f) (lower_mono (leOfHom h)) (Fin.last n)) (𝟙 K)
    exact familyMap_unselected (fun _ : Fin (n + 1) => f)
      (lower_mono (leOfHom h)) (Fin.last n) (notMem_last_lower T)

/-- The original final-coordinate arrow is constant at its codomain on the full upper slice. -/
def coordinateUpperIso {K L : C} (f : K ⟶ L) :
    upperFunctor n ⋙ coordinateCube f (Fin.last n) ≅ (Functor.const (Index n)).obj L := by
  refine eqToIso (Functor.hext ?_ ?_)
  · intro S
    change (if Fin.last n ∈ upper S then L else K) = L
    exact ite_eq_left (mem_last_upper S)
  · intro S T h
    change HEq (familyMap (fun _ : Fin (n + 1) => f) (upper_mono (leOfHom h)) (Fin.last n)) (𝟙 L)
    exact familyMap_selected (fun _ : Fin (n + 1) => f)
      (upper_mono (leOfHom h)) (Fin.last n) (mem_last_upper S)

/-- The lower final-coordinate comparison is the original domain identity with its original
transport. -/
theorem coordinateLowerIso_hom_heq {K L : C} (f : K ⟶ L) (S : Index n) :
    HEq ((coordinateLowerIso f).hom.app S) (𝟙 K) := by
  simp only [coordinateLowerIso, eqToIso.hom, eqToHom_app]
  exact eqToHom_heq_id_cod _ _ _

/-- The upper final-coordinate comparison is the original codomain identity with its
original transport. -/
theorem coordinateUpperIso_hom_heq {K L : C} (f : K ⟶ L) (S : Index n) :
    HEq ((coordinateUpperIso f).hom.app S) (𝟙 L) := by
  simp only [coordinateUpperIso, eqToIso.hom, eqToHom_app]
  exact eqToHom_heq_id_cod _ _ _

/-- The final-coordinate lower-to-upper face is the actual original arrow under both slice
comparisons. -/
@[reassoc] theorem coordinateIso_vertical {K L : C} (f : K ⟶ L) (S : Index n) :
    (coordinateCube f (Fin.last n)).map (homOfLE (lower_subset_upper S)) ≫
        (coordinateUpperIso f).hom.app S = (coordinateLowerIso f).hom.app S ≫ f := by
  have eK : (coordinateCube f (Fin.last n)).obj (lower S) = K :=
    ite_eq_right (notMem_last_lower S)
  have eL : (coordinateCube f (Fin.last n)).obj (upper S) = L :=
    ite_eq_left (mem_last_upper S)
  have hv := familyMap_added (fun _ : Fin (n + 1) => f)
    (lower_subset_upper S) (Fin.last n) (notMem_last_lower S) (mem_last_upper S)
  have hl := coordinateLowerIso_hom_heq f S
  have hu := coordinateUpperIso_hom_heq f S
  apply eq_of_heq
  exact ((heq_comp eK eL rfl hv hu).trans (heq_of_eq (Category.comp_id f))).trans
    ((heq_comp eK rfl rfl hl (HEq.rfl : HEq f f)).trans (heq_of_eq (Category.id_comp f))).symm

variable (F : Index n ⥤ C)

/-- The original lower-slice prefix retains the whole original preceding cube and every map. -/
def prefixLowerCubeIso : lowerFunctor n ⋙ (prefixFunctor n ⋙ F) ≅ F :=
  (Functor.associator (lowerFunctor n) (prefixFunctor n) F).symm ≪≫
    Functor.isoWhiskerRight (prefixLowerIso n) F ≪≫ Functor.leftUnitor F

/-- The original upper-slice prefix retains the whole original preceding cube and every map. -/
def prefixUpperCubeIso : upperFunctor n ⋙ (prefixFunctor n ⋙ F) ≅ F :=
  (Functor.associator (upperFunctor n) (prefixFunctor n) F).symm ≪≫
    Functor.isoWhiskerRight (prefixUpperIso n) F ≪≫ Functor.leftUnitor F

/-- Every original lower-prefix comparison is the image of its original index equality. -/
@[simp] theorem prefixLowerCubeIso_hom_app (S : Index n) :
    (prefixLowerCubeIso F).hom.app S = F.map (eqToHom (prefix_lower S)) := by
  simp [prefixLowerCubeIso, prefixLowerIso]

/-- Every original upper-prefix comparison is the image of its original index equality. -/
@[simp] theorem prefixUpperCubeIso_hom_app (S : Index n) :
    (prefixUpperCubeIso F).hom.app S = F.map (eqToHom (prefix_upper S)) := by
  simp [prefixUpperCubeIso, prefixUpperIso]

/-- The original prefix of a vertical face becomes the original identity under both comparisons. -/
@[reassoc] theorem prefixCubeIso_vertical (S : Index n) :
    F.map ((prefixFunctor n).map (homOfLE (lower_subset_upper S))) ≫
        (prefixUpperCubeIso F).hom.app S = (prefixLowerCubeIso F).hom.app S := by
  rw [prefixUpperCubeIso_hom_app, prefixLowerCubeIso_hom_app, ← F.map_comp]
  congr 1

variable [MonoidalCategory C]

/-- The full lower slice of a tensor step is the original cube tensored with the original
arrow domain. -/
def tensorStepLowerIso {K L : C} (f : K ⟶ L) : lowerCube (tensorStep F f) ≅ F ⋙ tensorRight K :=
  NatIso.ofComponents (fun S =>
    tensorIso ((prefixLowerCubeIso F).app S) ((coordinateLowerIso f).app S)) (by
    intro S T h
    change ((prefixFunctor n ⋙ F).map ((lowerFunctor n).map h) ⊗ₘ
        (coordinateCube f (Fin.last n)).map ((lowerFunctor n).map h)) ≫
          ((prefixLowerCubeIso F).hom.app T ⊗ₘ (coordinateLowerIso f).hom.app T) =
      ((prefixLowerCubeIso F).hom.app S ⊗ₘ (coordinateLowerIso f).hom.app S) ≫ (F.map h ▷ K)
    rw [← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · exact (prefixLowerCubeIso F).hom.naturality h
    · exact (coordinateLowerIso f).hom.naturality h)

/-- The full upper slice of a tensor step is the original cube tensored with the original
arrow codomain. -/
def tensorStepUpperIso {K L : C} (f : K ⟶ L) : upperCube (tensorStep F f) ≅ F ⋙ tensorRight L :=
  NatIso.ofComponents (fun S =>
    tensorIso ((prefixUpperCubeIso F).app S) ((coordinateUpperIso f).app S)) (by
    intro S T h
    change ((prefixFunctor n ⋙ F).map ((upperFunctor n).map h) ⊗ₘ
        (coordinateCube f (Fin.last n)).map ((upperFunctor n).map h)) ≫
          ((prefixUpperCubeIso F).hom.app T ⊗ₘ (coordinateUpperIso f).hom.app T) =
      ((prefixUpperCubeIso F).hom.app S ⊗ₘ (coordinateUpperIso f).hom.app S) ≫ (F.map h ▷ L)
    rw [← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · exact (prefixUpperCubeIso F).hom.naturality h
    · exact (coordinateUpperIso f).hom.naturality h)

/-- Every original vertical tensor face is the tensor of its original cube vertex with the
original arrow. -/
@[reassoc] theorem tensorStepIso_vertical {K L : C} (f : K ⟶ L) (S : Index n) :
    (verticalFaces (tensorStep F f)).app S ≫ (tensorStepUpperIso F f).hom.app S =
      (tensorStepLowerIso F f).hom.app S ≫ (F.obj S ◁ f) := by
  change (F.map ((prefixFunctor n).map (homOfLE (lower_subset_upper S))) ⊗ₘ
      (coordinateCube f (Fin.last n)).map (homOfLE (lower_subset_upper S))) ≫
        ((prefixUpperCubeIso F).hom.app S ⊗ₘ (coordinateUpperIso f).hom.app S) =
    ((prefixLowerCubeIso F).hom.app S ⊗ₘ (coordinateLowerIso f).hom.app S) ≫ (F.obj S ◁ f)
  rw [← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    prefixCubeIso_vertical, coordinateIso_vertical, Category.comp_id]

end TensorSlices

section BoundaryGlue

variable {n : ℕ} (F : Index (n + 1) ⥤ C) [HasColimit (punctured (upperCube F))]

/-- The original proper-face leg of a pair of lower-top and upper-boundary maps. -/
def glueComponent {Z : C} (l : F.obj (lower Finset.univ) ⟶ Z)
    (r : boundary (upperCube F) ⟶ Z) (S : Punctured (n + 1)) : F.obj S.1 ⟶ Z :=
  if h : Fin.last n ∈ S.1 then
    F.map (homOfLE (subset_upper_prefix S.1)) ≫
      boundaryι (upperCube F) ⟨«prefix» S.1, prefix_ne_univ S h⟩ ≫ r
  else
    F.map (homOfLE (subset_lower_univ S.1 h)) ≫ l

/-- Every lower leg factors through the original full lower-slice terminal vertex. -/
theorem glueComponent_lower {Z : C} (l : F.obj (lower Finset.univ) ⟶ Z)
    (r : boundary (upperCube F) ⟶ Z) (S : Index n) :
    glueComponent F l r ((lowerPunctured n).obj S) =
      F.map (homOfLE (lower_mono (Finset.subset_univ S))) ≫ l := by
  simp only [glueComponent, lowerPunctured, dite_eq_right (notMem_last_lower S)]

/-- Every proper upper leg is the original upper-boundary leg. -/
theorem glueComponent_upper {Z : C} (l : F.obj (lower Finset.univ) ⟶ Z)
    (r : boundary (upperCube F) ⟶ Z) (S : Punctured n) :
    glueComponent F l r ((upperPunctured n).obj S) = boundaryι (upperCube F) S ≫ r := by
  dsimp only [glueComponent, upperPunctured]
  rw [dite_eq_left (mem_last_upper S.1)]
  let t : Punctured n :=
    ⟨«prefix» (upper S.1), prefix_ne_univ ((upperPunctured n).obj S) (mem_last_upper S.1)⟩
  have h : S.1 ⊆ t.1 := le_of_eq (prefix_upper S.1).symm
  change F.map (homOfLE (subset_upper_prefix (upper S.1))) ≫ (boundaryι (upperCube F) t ≫ r) =
    boundaryι (upperCube F) S ≫ r
  exact boundaryι_naturality_assoc (upperCube F) (homOfLE h : S ⟶ t) r

variable [HasColimit (punctured (lowerCube F))]

/-- Compatibility on every original proper-face inclusion follows from the slice overlap
equation. -/
theorem glueComponent_naturality {Z : C} (l : F.obj (lower Finset.univ) ⟶ Z)
    (r : boundary (upperCube F) ⟶ Z)
    (comm : boundaryToTop (lowerCube F) ≫ l = boundaryMap (verticalFaces F) ≫ r)
    {S T : Punctured (n + 1)} (h : S.1 ⊆ T.1) :
    F.map (homOfLE h) ≫ glueComponent F l r T = glueComponent F l r S := by
  by_cases hS : Fin.last n ∈ S.1
  · have hT : Fin.last n ∈ T.1 := h hS
    let s : Punctured n := ⟨«prefix» S.1, prefix_ne_univ S hS⟩
    let t : Punctured n := ⟨«prefix» T.1, prefix_ne_univ T hT⟩
    have hst : s.1 ⊆ t.1 := prefix_mono h
    simp only [glueComponent, dite_eq_left hS, dite_eq_left hT]
    change F.map (homOfLE h) ≫
        (F.map (homOfLE (subset_upper_prefix T.1)) ≫ boundaryι (upperCube F) t ≫ r) =
      F.map (homOfLE (subset_upper_prefix S.1)) ≫ boundaryι (upperCube F) s ≫ r
    calc
      _ = F.map (homOfLE (subset_upper_prefix S.1)) ≫
          ((upperCube F).map (homOfLE hst : s ⟶ t) ≫ boundaryι (upperCube F) t) ≫ r := by
        dsimp only [upperCube, upperFunctor, Monotone.functor, Functor.comp_map]
        simp only [← Category.assoc]
        rw [← F.map_comp, ← F.map_comp]
        rfl
      _ = _ := congrArg (fun q => F.map (homOfLE (subset_upper_prefix S.1)) ≫ q ≫ r)
        (boundaryι_naturality (upperCube F) (homOfLE hst : s ⟶ t))
  · by_cases hT : Fin.last n ∈ T.1
    · let t : Punctured n := ⟨«prefix» T.1, prefix_ne_univ T hT⟩
      have hc : F.map (homOfLE (lower_mono (Finset.subset_univ («prefix» T.1)))) ≫ l =
          F.map (homOfLE (lower_subset_upper («prefix» T.1))) ≫ boundaryι (upperCube F) t ≫ r := by
        have hc := congrArg (fun q => boundaryι (lowerCube F) t ≫ q) comm
        rw [← Category.assoc, boundaryι_boundaryToTop, ← Category.assoc, boundaryι_map,
          Category.assoc] at hc
        exact hc
      simp only [glueComponent, dite_eq_right hS, dite_eq_left hT]
      change F.map (homOfLE h) ≫
          (F.map (homOfLE (subset_upper_prefix T.1)) ≫ boundaryι (upperCube F) t ≫ r) =
        F.map (homOfLE (subset_lower_univ S.1 hS)) ≫ l
      calc
        _ = F.map (homOfLE (subset_lower_prefix h hS)) ≫
            (F.map (homOfLE (lower_subset_upper («prefix» T.1))) ≫
              boundaryι (upperCube F) t ≫ r) := by
          simp only [← Category.assoc]
          rw [← F.map_comp, ← F.map_comp]
          rfl
        _ = F.map (homOfLE (subset_lower_prefix h hS)) ≫
            (F.map (homOfLE (lower_mono (Finset.subset_univ («prefix» T.1)))) ≫ l) :=
          congrArg (F.map (homOfLE (subset_lower_prefix h hS)) ≫ ·) hc.symm
        _ = _ := by
          rw [← Category.assoc, ← F.map_comp]
          rfl
    · simp only [glueComponent, dite_eq_right hS, dite_eq_right hT]
      rw [← Category.assoc, ← F.map_comp]
      rfl

/-- Every compatible pair of original lower-top and upper-boundary maps
extends to the full original punctured cube. -/
@[implicit_reducible]
def glueCocone {Z : C} (l : F.obj (lower Finset.univ) ⟶ Z)
    (r : boundary (upperCube F) ⟶ Z)
    (comm : boundaryToTop (lowerCube F) ≫ l = boundaryMap (verticalFaces F) ≫ r) :
    Cocone (punctured F) where
  pt := Z
  ι :=
    { app S := glueComponent F l r S
      naturality S T h := by
        change F.map (homOfLE (leOfHom h)) ≫ glueComponent F l r T = glueComponent F l r S ≫ 𝟙 Z
        rw [Category.comp_id]
        exact glueComponent_naturality F l r comm (leOfHom h) }

variable [HasColimit (punctured F)]

/-- The original slice union is a pushout in the original category,
including the complete descender and uniqueness on every original proper face. -/
def boundaryPushoutIsColimit : IsColimit (boundaryPushoutCocone F) :=
  PushoutCocone.IsColimit.mk (boundarySlices_condition F)
    (fun c => boundaryDesc F (glueCocone F c.inl c.inr c.condition))
    (fun c => by
      change boundaryι F ((lowerPunctured n).obj Finset.univ) ≫
        boundaryDesc F (glueCocone F c.inl c.inr c.condition) = c.inl
      rw [boundaryι_desc]
      change glueComponent F c.inl c.inr ((lowerPunctured n).obj Finset.univ) = c.inl
      rw [glueComponent_lower]
      simp only [homOfLE_refl, F.map_id, Category.id_comp])
    (fun c => by
      apply boundary_hom_ext (upperCube F)
      intro S
      rw [← Category.assoc, boundaryι_upperBoundaryInclusion, boundaryι_desc]
      exact glueComponent_upper F c.inl c.inr S)
    (fun c m hl hr => by
      apply boundary_hom_ext F
      intro S
      rw [boundaryι_desc]
      change boundaryι F S ≫ m = glueComponent F c.inl c.inr S
      by_cases hS : Fin.last n ∈ S.1
      · let s : Punctured n := ⟨«prefix» S.1, prefix_ne_univ S hS⟩
        have hleg : F.map (homOfLE (subset_upper_prefix S.1)) ≫
            (boundaryι (upperCube F) s ≫ upperBoundaryInclusion F) = boundaryι F S := by
          rw [boundaryι_upperBoundaryInclusion]
          exact boundaryι_naturality F (homOfLE (subset_upper_prefix S.1) :
            S ⟶ (upperPunctured n).obj s)
        simp only [glueComponent, dite_eq_left hS]
        change boundaryι F S ≫ m =
          F.map (homOfLE (subset_upper_prefix S.1)) ≫ boundaryι (upperCube F) s ≫ c.inr
        rw [← hleg]
        simp only [Category.assoc, hr]
      · have hleg : F.map (homOfLE (subset_lower_univ S.1 hS)) ≫ lowerTopInclusion F =
            boundaryι F S :=
          boundaryι_naturality F (homOfLE (subset_lower_univ S.1 hS) :
            S ⟶ (lowerPunctured n).obj Finset.univ)
        simp only [glueComponent, dite_eq_right hS]
        rw [← hleg, Category.assoc, hl])

end BoundaryGlue

section OneDimensionalBoundary

variable (F : Index 1 ⥤ C) [HasColimit (punctured F)]

/-- The actual one dimensional cube boundary is its original domain vertex. -/
def boundaryOneIso : boundary F ≅ F.obj ∅ :=
  (colimit.isColimit (punctured F)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal puncturedOneIsTerminal (punctured F))

/-- The original one dimensional face leg is the identity under its actual boundary comparison. -/
@[reassoc (attr := simp)] theorem boundaryOneIso_ι :
    boundaryι F puncturedOneEmpty ≫ (boundaryOneIso F).hom = 𝟙 (F.obj ∅) := by
  change (colimit.cocone (punctured F)).ι.app puncturedOneEmpty ≫ (boundaryOneIso F).hom
    = 𝟙 (F.obj ∅)
  rw [boundaryOneIso, IsColimit.comp_coconePointUniqueUpToIso_hom]
  change (punctured F).map (puncturedOneIsTerminal.from puncturedOneEmpty) = 𝟙 (F.obj ∅)
  rw [show puncturedOneIsTerminal.from puncturedOneEmpty = 𝟙 puncturedOneEmpty from
    Subsingleton.elim _ _, Functor.map_id]
  rfl

/-- The whole one dimensional attaching arrow is the original domain-to-codomain cube map. -/
def boundaryOneArrowIso : Arrow.mk (boundaryToTop F) ≅
    Arrow.mk (F.map (homOfLE (Finset.empty_subset Finset.univ))) :=
  Arrow.isoMk (boundaryOneIso F) (Iso.refl (F.obj Finset.univ)) (by
    change (boundaryOneIso F).hom ≫ F.map (homOfLE (Finset.empty_subset Finset.univ)) =
      boundaryToTop F ≫ 𝟙 (F.obj Finset.univ)
    apply boundary_hom_ext F
    intro S
    have hs := puncturedOne_eq_empty S
    subst S
    rw [← Category.assoc, boundaryOneIso_ι]
    have hr := (boundaryι_boundaryToTop_assoc F puncturedOneEmpty (𝟙 (F.obj Finset.univ))).trans
      (Category.comp_id _)
    exact (Category.id_comp _).trans hr.symm)

end OneDimensionalBoundary

section OneDimensionalTensor

/-- The one dimensional coordinate cube has exactly the original arrow as its full attaching map. -/
def coordinateCubeOneArrowIso {K L : C} (f : K ⟶ L)
    [HasColimit (punctured (coordinateCube f (0 : Fin 1)))] :
    Arrow.mk (boundaryToTop (coordinateCube f (0 : Fin 1))) ≅ Arrow.mk f := by
  let F : Index 1 ⥤ C := coordinateCube f (0 : Fin 1)
  have eK : F.obj ∅ = K := by
    change (if (0 : Fin 1) ∈ (∅ : Index 1) then L else K) = K
    exact ite_eq_right (Finset.notMem_empty (0 : Fin 1))
  have eL : F.obj Finset.univ = L := by
    change (if (0 : Fin 1) ∈ (Finset.univ : Index 1) then L else K) = L
    exact ite_eq_left (Finset.mem_univ (0 : Fin 1))
  refine boundaryOneArrowIso F ≪≫ Arrow.isoMk (eqToIso eK) (eqToIso eL) ?_
  change eqToHom eK ≫ f = F.map (homOfLE (Finset.empty_subset Finset.univ)) ≫ eqToHom eL
  have hg : HEq (F.map (homOfLE (Finset.empty_subset Finset.univ))) f :=
    familyMap_added (fun _ : Fin 1 => f) (Finset.empty_subset Finset.univ)
      (0 : Fin 1) (Finset.notMem_empty (0 : Fin 1)) (Finset.mem_univ (0 : Fin 1))
  have hn := (conj_eqToHom_iff_heq (F.map (homOfLE (Finset.empty_subset Finset.univ))) f eK
    eL).mpr hg
  rw [hn]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

variable [MonoidalCategory C] {K L : Fin 1 → C}

/-- The actual unary tensor cube has the original coordinate cube as its whole unary tensor
comparison. -/
def tensorCubeOneCoordinateIso (f : ∀ i, K i ⟶ L i) : tensorCube f ≅ coordinateCube (f
  0) (0 : Fin 1) :=
  NatIso.ofComponents (fun S => OrderedTensor.singletonIso (vertexFamily K L S)) (by
    intro S T h
    have h0 : familyMap f (leOfHom h) (0 : Fin 1) =
        (coordinateCube (f 0) (0 : Fin 1)).map h :=
      eq_of_heq (familyMap_coordinate f (leOfHom h) (0 : Fin 1))
    exact (OrderedTensor.singletonIso_naturality (familyMap f (leOfHom h))).trans
      (congrArg ((OrderedTensor.singletonIso (vertexFamily K L S)).hom ≫ ·) h0))

/-- The actual unary tensor cube attaching arrow is exactly the original arrow,
under the actual unitors and the actual punctured colimit. No unit cofibrancy is required. -/
def tensorCubeOneArrowIso (f : ∀ i, K i ⟶ L i) [HasColimitsOfShape (Punctured 1) C] :
    Arrow.mk (boundaryToTop (tensorCube f)) ≅ Arrow.mk (f 0) :=
  boundaryArrowIso (tensorCubeOneCoordinateIso f) ≪≫ coordinateCubeOneArrowIso (f 0)

end OneDimensionalTensor

section TensorStepBoundary

variable [MonoidalCategory C] {n : ℕ} (F : Index n ⥤ C) {K L : C} (f : K ⟶ L)

/-- The terminal tensor-step vertex is the original cube terminal tensored with the original
codomain. -/
def tensorStepTopIso : (tensorStep F f).obj Finset.univ ≅ F.obj Finset.univ ⊗ L :=
  eqToIso (congrArg (tensorStep F f).obj (upper_univ (n := n)).symm) ≪≫
    (tensorStepUpperIso F f).app Finset.univ

/-- Every original terminal-face map retains the full upper-slice terminal comparison. -/
@[reassoc] theorem tensorStepTopIso_map (S : Index (n + 1)) :
    (tensorStep F f).map (homOfLE (Finset.subset_univ S)) ≫ (tensorStepTopIso F f).hom =
      (tensorStep F f).map (homOfLE (by rw [upper_univ]; exact Finset.subset_univ S) :
        S ⟶ upper Finset.univ) ≫ (tensorStepUpperIso F f).hom.app Finset.univ := by
  rw [tensorStepTopIso, Iso.trans_hom, eqToIso.hom,
    ← eqToHom_map (tensorStep F f) (upper_univ (n := n)).symm, ← Category.assoc,
    ← (tensorStep F f).map_comp]
  congr 1

variable [HasColimitsOfShape (Punctured n) C]
variable [PreservesColimit (punctured F) (tensorRight K)]
variable [PreservesColimit (punctured F) (tensorRight L)]

omit [PreservesColimit (punctured F) (tensorRight L)] in
/-- The actual lower-slice boundary is the original boundary tensored with the original
arrow domain. -/
def tensorStepLowerBoundaryIso : boundary (lowerCube (tensorStep F f)) ≅ boundary F ⊗ K :=
  boundaryIso (tensorStepLowerIso F f) ≪≫ boundaryPostIso F (tensorRight K)

omit [PreservesColimit (punctured F) (tensorRight K)] in
/-- The actual upper-slice boundary is the original boundary tensored with the original
arrow codomain. -/
def tensorStepUpperBoundaryIso : boundary (upperCube (tensorStep F f)) ≅ boundary F ⊗ L :=
  boundaryIso (tensorStepUpperIso F f) ≪≫ boundaryPostIso F (tensorRight L)

omit [PreservesColimit (punctured F) (tensorRight L)] in
/-- Every original lower-boundary face is retained under the actual tensor comparison. -/
@[reassoc (attr := simp)] theorem tensorStepLowerBoundaryIso_ι (S : Punctured n) :
    boundaryι (lowerCube (tensorStep F f)) S ≫ (tensorStepLowerBoundaryIso F f).hom =
      (tensorStepLowerIso F f).hom.app S.1 ≫ (boundaryι F S ▷ K) := by
  rw [tensorStepLowerBoundaryIso, Iso.trans_hom, ← Category.assoc, boundaryι_iso,
    Category.assoc, boundaryι_postIso]
  rfl

omit [PreservesColimit (punctured F) (tensorRight K)] in
/-- Every original upper-boundary face is retained under the actual tensor comparison. -/
@[reassoc (attr := simp)] theorem tensorStepUpperBoundaryIso_ι (S : Punctured n) :
    boundaryι (upperCube (tensorStep F f)) S ≫ (tensorStepUpperBoundaryIso F f).hom =
      (tensorStepUpperIso F f).hom.app S.1 ≫ (boundaryι F S ▷ L) := by
  rw [tensorStepUpperBoundaryIso, Iso.trans_hom, ← Category.assoc, boundaryι_iso,
    Category.assoc, boundaryι_postIso]
  rfl

omit [PreservesColimit (punctured F) (tensorRight L)] in
/-- The original lower-slice attaching map is the original preceding attaching map tensored
with the domain. -/
@[reassoc] theorem tensorStepLowerBoundaryIso_toTop :
    boundaryToTop (lowerCube (tensorStep F f)) ≫ (tensorStepLowerIso F f).hom.app Finset.univ =
      (tensorStepLowerBoundaryIso F f).hom ≫ (boundaryToTop F ▷ K) := by
  apply boundary_hom_ext (lowerCube (tensorStep F f))
  intro S
  rw [← Category.assoc, boundaryι_boundaryToTop, ← Category.assoc, tensorStepLowerBoundaryIso_ι,
    Category.assoc, ← comp_whiskerRight, boundaryι_boundaryToTop]
  exact (tensorStepLowerIso F f).hom.naturality (homOfLE (Finset.subset_univ S.1))

omit [PreservesColimit (punctured F) (tensorRight K)] in
/-- The original upper-slice attaching map is the original preceding attaching map tensored
with the codomain. -/
@[reassoc] theorem tensorStepUpperBoundaryIso_toTop :
    boundaryToTop (upperCube (tensorStep F f)) ≫ (tensorStepUpperIso F f).hom.app Finset.univ =
      (tensorStepUpperBoundaryIso F f).hom ≫ (boundaryToTop F ▷ L) := by
  apply boundary_hom_ext (upperCube (tensorStep F f))
  intro S
  rw [← Category.assoc, boundaryι_boundaryToTop, ← Category.assoc, tensorStepUpperBoundaryIso_ι,
    Category.assoc, ← comp_whiskerRight, boundaryι_boundaryToTop]
  exact (tensorStepUpperIso F f).hom.naturality (homOfLE (Finset.subset_univ S.1))

/-- The original lower-to-upper boundary map is the tensor of the original boundary with the
original arrow. -/
@[reassoc] theorem tensorStepBoundaryIso_vertical :
    boundaryMap (verticalFaces (tensorStep F f)) ≫ (tensorStepUpperBoundaryIso F f).hom =
      (tensorStepLowerBoundaryIso F f).hom ≫ (boundary F ◁ f) := by
  apply boundary_hom_ext (lowerCube (tensorStep F f))
  intro S
  rw [← Category.assoc, boundaryι_map, Category.assoc, tensorStepUpperBoundaryIso_ι,
    ← Category.assoc]
  conv_rhs => rw [← Category.assoc, tensorStepLowerBoundaryIso_ι]
  rw [tensorStepIso_vertical, Category.assoc, whisker_exchange, ← Category.assoc]

/-- The original slice attachment span is the actual pushout-product span. -/
def tensorStepBoundarySpanIso :
    span (boundaryToTop (lowerCube (tensorStep F f))) (boundaryMap (verticalFaces
      (tensorStep F f))) ≅
      span (boundaryToTop F ▷ K) (boundary F ◁ f) :=
  spanExt (tensorStepLowerBoundaryIso F f) ((tensorStepLowerIso F f).app Finset.univ)
    (tensorStepUpperBoundaryIso F f) (tensorStepLowerBoundaryIso_toTop F f).symm
    (tensorStepBoundaryIso_vertical F f).symm

variable [HasColimitsOfShape (Punctured (n + 1)) C] [HasPushouts C]

/-- The actual tensor-step boundary is the source of the actual pushout product. -/
@[implicit_reducible]
def tensorStepBoundaryIso :
    boundary (tensorStep F f) ≅ pushout (boundaryToTop F ▷ K) (boundary F ◁ f) :=
  (boundaryPushoutIsColimit (tensorStep F f)).coconePointUniqueUpToIso
      (colimit.isColimit (span (boundaryToTop (lowerCube (tensorStep F f)))
        (boundaryMap (verticalFaces (tensorStep F f))))) ≪≫
    HasColimit.isoOfNatIso (tensorStepBoundarySpanIso F f)

/-- The actual lower-top inclusion is the original domain-side pushout-product inclusion. -/
@[reassoc (attr := simp)] theorem tensorStepBoundaryIso_lower :
    lowerTopInclusion (tensorStep F f) ≫ (tensorStepBoundaryIso F f).hom =
      (tensorStepLowerIso F f).hom.app Finset.univ ≫
        pushout.inl (boundaryToTop F ▷ K) (boundary F ◁ f) := by
  change (boundaryPushoutCocone (tensorStep F f)).ι.app WalkingSpan.left ≫
      (tensorStepBoundaryIso F f).hom =
    (tensorStepBoundarySpanIso F f).hom.app WalkingSpan.left ≫
      colimit.ι (span (boundaryToTop F ▷ K) (boundary F ◁ f)) WalkingSpan.left
  rw [tensorStepBoundaryIso, Iso.trans_hom, ← Category.assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact HasColimit.ι_isoOfNatIso_hom (tensorStepBoundarySpanIso F f) WalkingSpan.left

/-- The actual upper-boundary inclusion is the original codomain-side pushout-product inclusion. -/
@[reassoc (attr := simp)] theorem tensorStepBoundaryIso_upper :
    upperBoundaryInclusion (tensorStep F f) ≫ (tensorStepBoundaryIso F f).hom =
      (tensorStepUpperBoundaryIso F f).hom ≫
        pushout.inr (boundaryToTop F ▷ K) (boundary F ◁ f) := by
  change (boundaryPushoutCocone (tensorStep F f)).ι.app WalkingSpan.right ≫
      (tensorStepBoundaryIso F f).hom =
    (tensorStepBoundarySpanIso F f).hom.app WalkingSpan.right ≫
      colimit.ι (span (boundaryToTop F ▷ K) (boundary F ◁ f)) WalkingSpan.right
  rw [tensorStepBoundaryIso, Iso.trans_hom, ← Category.assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact HasColimit.ι_isoOfNatIso_hom (tensorStepBoundarySpanIso F f) WalkingSpan.right

/-- The actual tensor-step attaching arrow is the actual pushout product of the original
preceding attaching arrow and the original final-coordinate arrow. -/
def tensorStepArrowIso :
    Arrow.mk (boundaryToTop (tensorStep F f)) ≅ Arrow.mk (boundaryToTop F) □ Arrow.mk f := by
  change Arrow.mk (boundaryToTop (tensorStep F f)) ≅
    Arrow.mk (pushout.desc (F.obj Finset.univ ◁ f) (boundaryToTop F ▷ L)
      (whisker_exchange (boundaryToTop F) f).symm)
  exact Arrow.isoMk (tensorStepBoundaryIso F f) (tensorStepTopIso F f) (by
    change (tensorStepBoundaryIso F f).hom ≫
        pushout.desc (F.obj Finset.univ ◁ f) (boundaryToTop F ▷ L)
          (whisker_exchange (boundaryToTop F) f).symm =
      boundaryToTop (tensorStep F f) ≫ (tensorStepTopIso F f).hom
    apply PushoutCocone.IsColimit.hom_ext (boundaryPushoutIsColimit (tensorStep F f))
    · change lowerTopInclusion (tensorStep F f) ≫
          ((tensorStepBoundaryIso F f).hom ≫
            pushout.desc (F.obj Finset.univ ◁ f) (boundaryToTop F ▷ L)
              (whisker_exchange (boundaryToTop F) f).symm) =
        lowerTopInclusion (tensorStep F f) ≫
          (boundaryToTop (tensorStep F f) ≫ (tensorStepTopIso F f).hom)
      rw [← Category.assoc, tensorStepBoundaryIso_lower, Category.assoc, pushout.inl_desc,
        ← Category.assoc]
      change (tensorStepLowerIso F f).hom.app Finset.univ ≫ (F.obj Finset.univ ◁ f) =
        (boundaryι (tensorStep F f) ((lowerPunctured n).obj Finset.univ) ≫
          boundaryToTop (tensorStep F f)) ≫ (tensorStepTopIso F f).hom
      rw [boundaryι_boundaryToTop, tensorStepTopIso_map]
      exact (tensorStepIso_vertical F f Finset.univ).symm
    · change upperBoundaryInclusion (tensorStep F f) ≫
          ((tensorStepBoundaryIso F f).hom ≫
            pushout.desc (F.obj Finset.univ ◁ f) (boundaryToTop F ▷ L)
              (whisker_exchange (boundaryToTop F) f).symm) =
        upperBoundaryInclusion (tensorStep F f) ≫
          (boundaryToTop (tensorStep F f) ≫ (tensorStepTopIso F f).hom)
      rw [← Category.assoc, tensorStepBoundaryIso_upper, Category.assoc, pushout.inr_desc,
        ← tensorStepUpperBoundaryIso_toTop]
      apply boundary_hom_ext (upperCube (tensorStep F f))
      intro S
      rw [← Category.assoc, boundaryι_boundaryToTop]
      conv_rhs =>
        rw [← Category.assoc, boundaryι_upperBoundaryInclusion, ← Category.assoc,
          boundaryι_boundaryToTop, tensorStepTopIso_map]
      rfl)

end TensorStepBoundary

/-- The zero dimensional boundary is initial, for every original zero cube. -/
def boundaryZeroIsInitial (F : Index 0 ⥤ C) [HasColimit (punctured F)] :
    IsInitial (boundary F) :=
  (isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (punctured F))) (colimit.isColimit
    (punctured F))

section AlternatingIteration

variable [MonoidalCategory C] [HasInitial C] [HasPushouts C]

/-- Iterate the original arrows in their original order, retaining every
original coefficient as a tensor factor. Degree zero is the original initial-to-coefficient
arrow. -/
def iteratedAlternatingArrow : {n : ℕ} → (Fin (n + 1) → C) →
    {K L : Fin n → C} → (∀ i, K i ⟶ L i) → Arrow C
  | 0, A, _, _, _ => Arrow.mk (initial.to (A 0))
  | n + 1, A, _, _, f =>
      (tensorRight (A (Fin.last (n + 1)))).mapArrow.obj
        (iteratedAlternatingArrow (fun i : Fin (n + 1) => A i.castSucc)
          (fun i : Fin n => f i.castSucc) □ Arrow.mk (f (Fin.last n)))

variable [HasColimitsOfSize.{0, 0} C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The actual alternating cube attaching arrow is its actual recursive
pushout product of all original arrows with all original coefficient factors.
The comparison constructs both maps and includes degree zero. -/
def alternatingBoundaryArrowIso : {n : ℕ} → (A : Fin (n + 1) → C) →
    {K L : Fin n → C} → (f : ∀ i, K i ⟶ L i) →
      Arrow.mk (boundaryToTop (alternatingCube A f)) ≅ iteratedAlternatingArrow A f
  | 0, A, _, _, f =>
      Arrow.isoMk ((boundaryZeroIsInitial (alternatingCube A f)).uniqueUpToIso initialIsInitial)
        (Iso.refl (A 0)) (by
          exact (boundaryZeroIsInitial (alternatingCube A f)).hom_ext _ _)
  | n + 1, A, _, _, f =>
      boundaryArrowIso (alternatingCubeStepIso A f) ≪≫
        boundaryPostArrowIso
          (tensorStep (alternatingCube (fun i : Fin (n + 1) => A i.castSucc)
            (fun i : Fin n => f i.castSucc)) (f (Fin.last n)))
          (tensorRight (A (Fin.last (n + 1)))) ≪≫
        (tensorRight (A (Fin.last (n + 1)))).mapArrow.mapIso
          (tensorStepArrowIso (alternatingCube (fun i : Fin (n + 1) => A i.castSucc)
            (fun i : Fin n => f i.castSucc)) (f (Fin.last n))) ≪≫
        (tensorRight (A (Fin.last (n + 1)))).mapArrow.mapIso
          ((Arrow.pushoutProduct.mapIso
            (alternatingBoundaryArrowIso (fun i : Fin (n + 1) => A i.castSucc)
              (fun i : Fin n => f i.castSucc))).app (Arrow.mk (f (Fin.last n))))

end AlternatingIteration

section CoefficientGrouping

variable [MonoidalCategory C]

/-- Tensor all original coefficients in their original order, with no extra degree-zero unit
factor. -/
def coefficientObj : {n : ℕ} → (Fin (n + 1) → C) → C
  | 0, A => A 0
  | n + 1, A => coefficientObj (fun i : Fin (n + 1) => A i.castSucc) ⊗ A (Fin.last (n + 1))

/-- The original associator combines two consecutive original coefficient tensor factors. -/
def tensorRightTwiceArrowIso (g : Arrow C) (U V : C) :
    (tensorRight V).mapArrow.obj ((tensorRight U).mapArrow.obj g) ≅
      (tensorRight (U ⊗ V)).mapArrow.obj g :=
  Arrow.isoMk (α_ g.left U V) (α_ g.right U V) (by
    exact (associator_naturality_left g.hom U V).symm)

variable [BraidedCategory C] [HasPushouts C]

/-- Move an arbitrary original right coefficient past one original pushout-product factor,
using the actual braiding and the actual preserved pushout. -/
def pushoutProductTensorRightIso (g h : Arrow C) (U : C)
    [PreservesColimit (span (h.hom ▷ g.left) (h.left ◁ g.hom)) (tensorRight U)] :
    ((tensorRight U).mapArrow.obj g □ h) ≅ (tensorRight U).mapArrow.obj (g □ h) :=
  Arrow.PushoutProduct.braiding ((tensorRight U).mapArrow.obj g) h ≪≫
    (Arrow.PushoutProduct.whiskerRightIso h g (W := U)).symm ≪≫
    (tensorRight U).mapArrow.mapIso (Arrow.PushoutProduct.braiding h g)

variable [HasColimitsOfSize.{0, 0} C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The literal alternating cube attaching arrow is the original pure-letter cube
attaching arrow tensored with all original coefficients in their original order.
All original tensor factors, arrows, and degree-zero data are retained. -/
def alternatingCubeCoefficientIso : {n : ℕ} → (A : Fin (n + 1) → C) →
    {K L : Fin n → C} → (f : ∀ i, K i ⟶ L i) →
      Arrow.mk (boundaryToTop (alternatingCube A f)) ≅
        (tensorRight (coefficientObj A)).mapArrow.obj (Arrow.mk (boundaryToTop (tensorCube f)))
  | 0, A, _, _, f =>
      Arrow.isoMk
        ((boundaryZeroIsInitial (alternatingCube A f)).uniqueUpToIso
          ((boundaryZeroIsInitial (tensorCube f)).isInitialObj
            (tensorRight (A 0)) (boundary (tensorCube f))))
        (λ_ (A 0)).symm (by exact (boundaryZeroIsInitial (alternatingCube A f)).hom_ext _ _)
  | n + 1, A, _, _, f =>
      boundaryArrowIso (alternatingCubeStepIso A f) ≪≫
        boundaryPostArrowIso
          (tensorStep (alternatingCube (fun i : Fin (n + 1) => A i.castSucc)
            (fun i : Fin n => f i.castSucc)) (f (Fin.last n)))
          (tensorRight (A (Fin.last (n + 1)))) ≪≫
        (tensorRight (A (Fin.last (n + 1)))).mapArrow.mapIso
          (tensorStepArrowIso (alternatingCube (fun i : Fin (n + 1) => A i.castSucc)
            (fun i : Fin n => f i.castSucc)) (f (Fin.last n))) ≪≫
        (tensorRight (A (Fin.last (n + 1)))).mapArrow.mapIso
          ((Arrow.pushoutProduct.mapIso
            (alternatingCubeCoefficientIso (fun i : Fin (n + 1) => A i.castSucc)
              (fun i : Fin n => f i.castSucc))).app (Arrow.mk (f (Fin.last n)))) ≪≫
        (tensorRight (A (Fin.last (n + 1)))).mapArrow.mapIso
          (pushoutProductTensorRightIso
            (Arrow.mk (boundaryToTop (tensorCube (fun i : Fin n => f i.castSucc))))
            (Arrow.mk (f (Fin.last n)))
            (coefficientObj (fun i : Fin (n + 1) => A i.castSucc))) ≪≫
        tensorRightTwiceArrowIso
          (Arrow.mk (boundaryToTop (tensorCube (fun i : Fin n => f i.castSucc))) □
            Arrow.mk (f (Fin.last n)))
          (coefficientObj (fun i : Fin (n + 1) => A i.castSucc)) (A (Fin.last (n + 1))) ≪≫
        (tensorRight (coefficientObj A)).mapArrow.mapIso
          ((tensorStepArrowIso (tensorCube (fun i : Fin n =>
            f i.castSucc)) (f (Fin.last n))).symm ≪≫
            (boundaryArrowIso (tensorCubeStepIso f)).symm)

end CoefficientGrouping

section PushoutProductIteration

variable [MonoidalCategory C] [HasInitial C] [HasPushouts C]

/-- The iterated pushout product of the original finite family of arrows in
its original order. Degree one is the original arrow itself; degree zero is the
initial-to-unit arrow. -/
def iteratedPushoutProduct : {n : ℕ} → {K L : Fin n → C} → (∀ i, K i ⟶ L i) → Arrow C
  | 0, _, _, _ => Arrow.mk (initial.to (𝟙_ C))
  | 1, _, _, f => Arrow.mk (f 0)
  | n + 2, _, _, f => iteratedPushoutProduct (fun i : Fin (n + 1) => f i.castSucc) □
      Arrow.mk (f (Fin.last (n + 1)))

variable [HasColimitsOfSize.{0, 0} C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original pure-letter cube attaching arrow is the iterated pushout product
of exactly its original arrows, with the original degree-one arrow and degree-zero unit
convention. -/
def tensorBoundaryArrowIso : {n : ℕ} → {K L : Fin n → C} → (f : ∀ i, K i ⟶ L i) →
    Arrow.mk (boundaryToTop (tensorCube f)) ≅ iteratedPushoutProduct f
  | 0, _, _, f =>
      Arrow.isoMk ((boundaryZeroIsInitial (tensorCube f)).uniqueUpToIso initialIsInitial)
        (Iso.refl (𝟙_ C)) (by exact (boundaryZeroIsInitial (tensorCube f)).hom_ext _ _)
  | 1, _, _, f => tensorCubeOneArrowIso f
  | n + 2, _, _, f =>
      boundaryArrowIso (tensorCubeStepIso f) ≪≫
        tensorStepArrowIso (tensorCube (fun i : Fin (n + 1) =>
          f i.castSucc)) (f (Fin.last (n + 1))) ≪≫
        (Arrow.pushoutProduct.mapIso
          (tensorBoundaryArrowIso (fun i : Fin (n + 1) => f i.castSucc))).app
            (Arrow.mk (f (Fin.last (n + 1))))

variable [BraidedCategory C]

/-- The actual alternating cube attaching arrow is the iterated pushout product
of the original letter arrows tensored with all original coefficient factors.
Both comparison maps are constructed for every degree, including zero and one. -/
def alternatingPushoutProductIso {n : ℕ} (A : Fin (n + 1) → C) {K L : Fin n → C}
    (f : ∀ i, K i ⟶ L i) :
    Arrow.mk (boundaryToTop (alternatingCube A f)) ≅
      (tensorRight (coefficientObj A)).mapArrow.obj (iteratedPushoutProduct f) :=
  alternatingCubeCoefficientIso A f ≪≫
    (tensorRight (coefficientObj A)).mapArrow.mapIso (tensorBoundaryArrowIso f)

end PushoutProductIteration

#print axioms familyCube
#print axioms alternatingCube
#print axioms boundaryMap
#print axioms boundaryPushoutIsColimit
#print axioms tensorStepArrowIso
#print axioms tensorCubeOneArrowIso
#print axioms tensorBoundaryArrowIso
#print axioms alternatingPushoutProductIso

end CategoryTheory.MonoidalCategory.FiniteCube
