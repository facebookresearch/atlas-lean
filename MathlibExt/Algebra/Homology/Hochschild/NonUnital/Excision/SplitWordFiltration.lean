/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWords
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarAssociatedGraded
public meta import Lean.Elab.Tactic.Omega

/-!
# Ideal-count stages in split-word coordinates

For a colour word c, its ideal-position count is the number of false positions and its
quotient-position count the number of true positions; their sum is the word length N. A tensor
span requiring r ideal entries is exactly the inverse image of the colour-coordinate submodule
supported on colours with at least r false positions.

In the relative naive and positive coefficient bar kernels, stage p therefore has zero
coordinates on every colour with more than p quotient positions. Coordinates with exactly p
quotient positions vanish on the predecessor stage, so they descend to the associated layer.

The descended maps collect a finite family of exact-count colour coordinates. They are
degreewise module maps; their definitions do not assert a chain-complex isomorphism. The
coefficient V remains arbitrary.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

/-- For c : Fin N → Bool, splitWordIdealPositionCount c is the cardinality of {i : Fin N | c i =
false}. -/
def splitWordIdealPositionCount {N : ℕ} (colour : Fin N → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => colour i = false)).card

/-- For c : Fin N → Bool, quotientEntryCount c + splitWordIdealPositionCount c = N. The true and
false fibres partition Fin N. -/
theorem splitWordPositionCounts_add {N : ℕ} (colour : Fin N → Bool) :
    quotientEntryCount colour + splitWordIdealPositionCount colour = N := by
  classical
  have hfalse :
      Finset.univ.filter (fun i : Fin N => ¬ colour i = true) =
        Finset.univ.filter (fun i : Fin N => colour i = false) := by
    apply Finset.ext
    intro i
    cases colour i <;> simp
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun i => colour i = true)
  rw [hfalse, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- For p,N : ℕ, splitWordGradeColours p N is {c : Fin N → Bool // quotientEntryCount c = p}, the
subtype of masks with exactly p quotient positions. -/
abbrev splitWordGradeColours (p N : ℕ) :=
  {colour : Fin N → Bool // quotientEntryCount colour = p}

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (splitting : I.KSplit)

variable {N : ℕ}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For a : Fin N → A, if
the number of its entries lying in I exceeds the number of false positions of c, then
P_c(tprod a) = 0. Some ideal entry must be read by a quotient projection. -/
theorem splitAmbientToWord_tprod_zero_of_count (colour : Fin N → Bool) (a : Fin N → A)
    (ha : splitWordIdealPositionCount colour < idealEntryCount k A I a) :
    splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) = 0 := by
  classical
  by_cases h : ∃ i : Fin N, colour i = true ∧ a i ∈ I.toSubmodule
  · rcases h with ⟨i, hi, hai⟩
    rw [splitAmbientToWord_tprod]
    exact (PiTensorProduct.tprod k).map_coord_zero i
      (splitWordPositionProjection_ideal_zero k A I splitting colour i hi (a i) hai)
  · have hs : (Finset.univ.filter (fun i : Fin N => a i ∈ I.toSubmodule)) ⊆
        Finset.univ.filter (fun i => colour i = false) := by
      intro i hi
      have hai := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      cases hc : colour i
      · rfl
      · exact False.elim (h ⟨i, hc, hai⟩)
    have hc := Finset.card_le_card hs
    change idealEntryCount k A I a ≤ splitWordIdealPositionCount colour at hc
    omega

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. If c has fewer than r
false positions, idealWordSpan N r ≤ ker P_c. Every tensor word with at least r ideal entries
therefore has zero c-coordinate. -/
theorem idealWordSpan_le_ker_splitAmbientToWord (colour : Fin N → Bool) (required : ℕ)
    (h : splitWordIdealPositionCount colour < required) :
    idealWordSpan k A I N required ≤
      LinearMap.ker (splitAmbientToWord k A I splitting colour) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  change splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) = 0
  exact splitAmbientToWord_tprod_zero_of_count k A I splitting colour a (h.trans_le ha)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem splitWordEntryMap_mem_ideal (colour : Bool) (h : colour = false)
    (a : splitWordEntry k A I colour) :
    splitWordEntryMap k A I splitting colour a ∈ I.toSubmodule := by
  cases colour with
  | false => exact a.property
  | true => cases h

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. If r ≤
splitWordIdealPositionCount c, then range J_c ≤ idealWordSpan N r. -/
theorem splitWordToAmbient_range_le_idealWordSpan (colour : Fin N → Bool) (required : ℕ)
    (h : required ≤ splitWordIdealPositionCount colour) :
    LinearMap.range (splitWordToAmbient k A I splitting colour) ≤
      idealWordSpan k A I N required := by
  classical
  rw [splitWordToAmbient, PiTensorProduct.map_range_eq_span_tprod]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun i => splitWordPositionMap k A I splitting colour i (a i), ?_, rfl⟩
  have hs : (Finset.univ.filter (fun i : Fin N => colour i = false)) ⊆
      Finset.univ.filter
        (fun i => splitWordPositionMap k A I splitting colour i (a i) ∈ I.toSubmodule) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    exact splitWordEntryMap_mem_ideal k A I splitting (colour i)
      (Finset.mem_filter.mp hi).2 (a i)
  exact h.trans (Finset.card_le_card hs)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q.
splitWordCoordinateStage N r is the submodule of Π c, W_c consisting of families x with x_c =
0 whenever c has fewer than r false positions. -/
def splitWordCoordinateStage (N required : ℕ) : Submodule k (splitWordCoordinates k A I N) where
  carrier := {x | ∀ colour : Fin N → Bool,
    splitWordIdealPositionCount colour < required → x colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : splitWordTensor k A I colour)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' := fun r x hx colour hc => by
    change r • x colour = (0 : splitWordTensor k A I colour)
    rw [hx colour hc, smul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For N,r : ℕ,
idealWordSpan N r equals the inverse image of splitWordCoordinateStage N r under the
all-colour map x ↦ (P_c(x)). -/
theorem idealWordSpan_eq_splitWordCoordinateStage_comap (N required : ℕ) :
    idealWordSpan k A I N required =
      (splitWordCoordinateStage k A I N required).comap
        (ambientToSplitWordCoordinates k A I splitting N) := by
  classical
  apply le_antisymm
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        splitAmbientToWord k A I splitting colour x = 0
    intro colour hc
    exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour required hc hx
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        splitAmbientToWord k A I splitting colour x = 0 at hx
    rw [← splitWord_reconstruct k A I splitting x]
    apply Submodule.sum_mem
    intro colour _
    by_cases hc : required ≤ splitWordIdealPositionCount colour
    · exact splitWordToAmbient_range_le_idealWordSpan k A I splitting colour required hc
        ⟨splitAmbientToWord k A I splitting colour x, rfl⟩
    · rw [hx colour (Nat.lt_of_not_ge hc), map_zero]
      exact Submodule.zero_mem _

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For p,n : ℕ,
F_p equals the inverse image of splitWordCoordinateStage (n + 1) (n + 1 − p) under all colour
projections composed with W_n. -/
theorem naiveWordFiltration_eq_splitWordCoordinateStage_comap (p n : ℕ) :
    naiveWordFiltration k A I p n =
      (splitWordCoordinateStage k A I (n + 1) (n + 1 - p)).comap
        ((ambientToSplitWordCoordinates k A I splitting (n + 1)).comp
          (relativeNaiveWordMap k A I n)) := by
  unfold naiveWordFiltration
  rw [idealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For c : Fin (n
+ 1) → Bool, naiveStageToSplitWord p n c is P_c ∘ W_n restricted to F_p, with target the
coloured word tensor W_c. -/
def naiveStageToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool) :
    naiveWordFiltration k A I p n →ₗ[k] splitWordTensor k A I colour :=
  (splitAmbientToWord k A I splitting colour).comp
    ((relativeNaiveWordMap k A I n).comp (naiveWordFiltration k A I p n).subtype)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. If p <
quotientEntryCount c, naiveStageToSplitWord p n c x = 0 for every x : F_p. -/
theorem naiveStageToSplitWord_zero_of_quotient_count (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (h : p < quotientEntryCount colour)
    (x : naiveWordFiltration k A I p n) :
    naiveStageToSplitWord k A I splitting p n colour x = 0 := by
  have hc := splitWordPositionCounts_add colour
  have hrequired : splitWordIdealPositionCount colour < n + 1 - p := by omega
  have hxw : relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x) ∈
      idealWordSpan k A I (n + 1) (n + 1 - p) := Submodule.mem_comap.mp x.property
  change splitAmbientToWord k A I splitting colour
    (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
  exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour (n + 1 - p)
    hrequired hxw

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For x : F_p, ∑
c : Fin (n + 1) → Bool, J_c(naiveStageToSplitWord p n c x) = W_n(x.val). -/
theorem naiveStage_splitWord_reconstruct (p n : ℕ)
    (x : naiveWordFiltration k A I p n) :
    (∑ colour : Fin (n + 1) → Bool,
      splitWordToAmbient k A I splitting colour
        (naiveStageToSplitWord k A I splitting p n colour x)) =
      relativeNaiveWordMap k A I n x.val :=
  splitWord_reconstruct k A I splitting (relativeNaiveWordMap k A I n x.val)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. If c has
quotientEntryCount c = p, the predecessor F_lower, viewed as a submodule of F_p, lies in the
kernel of naiveStageToSplitWord p n c. Here F_lower is zero at p = 0 and F_(p−1) otherwise. -/
theorem naiveLowerFiltration_le_ker_stageToSplitWord (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (hcolour : quotientEntryCount colour = p) :
    (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype ≤
      LinearMap.ker (naiveStageToSplitWord k A I splitting p n colour) := by
  intro x hx
  change naiveStageToSplitWord k A I splitting p n colour x = 0
  have hxl : (naiveWordFiltration k A I p n).subtype x ∈
      naiveLowerFiltration k A I p n := Submodule.mem_comap.mp hx
  by_cases hp : p = 0
  · rw [naiveLowerFiltration, ite_eq_left hp] at hxl
    have hx0 : (naiveWordFiltration k A I p n).subtype x = 0 := by
      simpa only [Submodule.mem_bot] using hxl
    change splitAmbientToWord k A I splitting colour
      (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
    rw [hx0, map_zero, map_zero]
  · rw [naiveLowerFiltration, ite_eq_right hp] at hxl
    have hxw : relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x) ∈
        idealWordSpan k A I (n + 1) (n + 1 - (p - 1)) := Submodule.mem_comap.mp hxl
    have hc := splitWordPositionCounts_add colour
    have hrequired : splitWordIdealPositionCount colour < n + 1 - (p - 1) := by omega
    change splitAmbientToWord k A I splitting colour
      (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
    exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour
      (n + 1 - (p - 1)) hrequired hxw

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For c with
quotientEntryCount c = p, naiveLayerToSplitWord maps F_p/F_lower to W_c, induced by P_c ∘ W_n
after the predecessor-kernel inclusion. -/
def naiveLayerToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) :
    naiveWordLayer k A I p n →ₗ[k] splitWordTensor k A I colour :=
  ((naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype).liftQ
    (naiveStageToSplitWord k A I splitting p n colour)
    (naiveLowerFiltration_le_ker_stageToSplitWord k A I splitting p n colour hcolour)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For c with
quotient count p and x : F_p, naiveLayerToSplitWord c ([x]) = P_c(W_n(x.val)). -/
theorem naiveLayerToSplitWord_projection (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) (x : naiveWordFiltration k A I p n) :
    naiveLayerToSplitWord k A I splitting p n colour hcolour
        (naiveWordLayerProjection k A I p n x) =
      splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) := rfl

/-- Let k be commutative, I a nonunital k-subalgebra of A and W_c the tensor word with I at false
positions and A/I at true positions. For p,n : ℕ, naiveSplitWordGradeCoordinates is Π c :
splitWordGradeColours p (n + 1), W_c. -/
abbrev naiveSplitWordGradeCoordinates (p n : ℕ) : Type (max u v) :=
  ∀ colour : splitWordGradeColours p (n + 1), splitWordTensor k A I colour.val

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map.
naiveLayerToSplitWordCoordinates maps naiveWordLayer p n to Π c with quotient count p, W_c by
all descended P_c ∘ W_n maps. -/
def naiveLayerToSplitWordCoordinates (p n : ℕ) :
    naiveWordLayer k A I p n →ₗ[k] naiveSplitWordGradeCoordinates k A I p n :=
  LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    naiveLayerToSplitWord k A I splitting p n colour.val colour.property)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map.
naiveAssociatedSplitWordMap p n is the degreewise module morphism from
(naiveAssociatedWordComplex p).X n to ModuleCat.of k (naiveSplitWordGradeCoordinates p n). Its
underlying map collects the descended colour coordinates. -/
def naiveAssociatedSplitWordMap (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).X n ⟶
      ModuleCat.of k (naiveSplitWordGradeCoordinates k A I p n) :=
  ModuleCat.ofHom (naiveLayerToSplitWordCoordinates k A I splitting p n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Choose a k-linear quotient section s. Let W_n : K_b,n → A^⊗(n+1) be the relative
naive word inclusion and F_p its ideal-count stage requiring n + 1 − p ideal entries. For a
colour c, let W_c tensor I at false positions and A/I at true positions; let J_c tensor
inclusion or section and P_c tensor the split ideal projection or quotient map. For x : F_p
and c with quotient count p, the c-coordinate of naiveLayerToSplitWordCoordinates([x]) is
P_c(W_n(x.val)). -/
theorem naiveLayerToSplitWordCoordinates_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p n) (colour : splitWordGradeColours p (n + 1)) :
    naiveLayerToSplitWordCoordinates k A I splitting p n
        (naiveWordLayerProjection k A I p n x) colour =
      splitAmbientToWord k A I splitting colour.val (relativeNaiveWordMap k A I n x.val) := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be any k-module
and P_c^V = id_V ⊗ P_c. If c has fewer than r false positions, coefficientIdealWordSpan N r ≤
ker P_c^V. -/
theorem coefficientIdealWordSpan_le_ker_splitAmbientToWord (colour : Fin N → Bool)
    (required : ℕ) (h : splitWordIdealPositionCount colour < required) :
    coefficientIdealWordSpan k A I V N required ≤
      LinearMap.ker (coefficientSplitAmbientToWord k A I V splitting colour) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, a, ha, rfl⟩
  change coefficientSplitAmbientToWord k A I V splitting colour
    (v ⊗ₜ[k] PiTensorProduct.tprod k a) = 0
  rw [coefficientSplitAmbientToWord, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [splitAmbientToWord_tprod_zero_of_count k A I splitting colour a (h.trans_le ha),
    TensorProduct.tmul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For any k-module V, if
r ≤ splitWordIdealPositionCount c, range(id_V ⊗ J_c) ≤ coefficientIdealWordSpan N r. -/
theorem coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
    (colour : Fin N → Bool) (required : ℕ)
    (h : required ≤ splitWordIdealPositionCount colour) :
    LinearMap.range (coefficientSplitWordToAmbient k A I V splitting colour) ≤
      coefficientIdealWordSpan k A I V N required := by
  rw [coefficientSplitWordToAmbient, TensorProduct.range_map_eq_span_tmul]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, y, rfl⟩
  have hy : splitWordToAmbient k A I splitting colour y ∈ idealWordSpan k A I N required :=
    splitWordToAmbient_range_le_idealWordSpan k A I splitting colour required h ⟨y, rfl⟩
  have hv : idealWordSpan k A I N required ≤
      (coefficientIdealWordSpan k A I V N required).comap
        (TensorProduct.mk k V (TensorPower k N A) v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨v, a, ha, rfl⟩
  have hmem := hv hy
  change v ⊗ₜ[k] splitWordToAmbient k A I splitting colour y ∈
    coefficientIdealWordSpan k A I V N required at hmem
  change v ⊗ₜ[k] splitWordToAmbient k A I splitting colour y ∈
    coefficientIdealWordSpan k A I V N required
  exact hmem

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For a k-module V,
coefficientSplitWordCoordinateStage N r is the submodule of Π c, V ⊗[k] W_c whose c-coordinate
is zero when c has fewer than r false positions. -/
def coefficientSplitWordCoordinateStage (N required : ℕ) :
    Submodule k (coefficientSplitWordCoordinates k A I V N) where
  carrier := {x | ∀ colour : Fin N → Bool,
    splitWordIdealPositionCount colour < required → x colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : V ⊗[k] splitWordTensor k A I colour)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' := fun r x hx colour hc => by
    change r • x colour = (0 : V ⊗[k] splitWordTensor k A I colour)
    rw [hx colour hc, smul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For any k-module V and
N,r : ℕ, coefficientIdealWordSpan N r equals the inverse image of
coefficientSplitWordCoordinateStage N r under x ↦ ((id_V ⊗ P_c)(x))_c. -/
theorem coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap (N required : ℕ) :
    coefficientIdealWordSpan k A I V N required =
      (coefficientSplitWordCoordinateStage k A I V N required).comap
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N) := by
  classical
  apply le_antisymm
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        coefficientSplitAmbientToWord k A I V splitting colour x = 0
    intro colour hc
    exact coefficientIdealWordSpan_le_ker_splitAmbientToWord
      k A I splitting V colour required hc hx
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        coefficientSplitAmbientToWord k A I V splitting colour x = 0 at hx
    rw [← coefficientSplitWord_reconstruct k A I V splitting x]
    apply Submodule.sum_mem
    intro colour _
    by_cases hc : required ≤ splitWordIdealPositionCount colour
    · exact coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
        k A I splitting V colour required hc
        ⟨coefficientSplitAmbientToWord k A I V splitting colour x, rfl⟩
    · rw [hx colour (Nat.lt_of_not_ge hc), map_zero]
      exact Submodule.zero_mem _

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. The stage B_p equals the
inverse image of coefficientSplitWordCoordinateStage (n + 1) (n + 1 − p) under the complete
colour map after W_n^V. -/
theorem barWordFiltration_eq_splitWordCoordinateStage_comap (p n : ℕ) :
    barWordFiltration k A I V p n =
      (coefficientSplitWordCoordinateStage k A I V (n + 1) (n + 1 - p)).comap
        ((coefficientAmbientToSplitWordCoordinates k A I V splitting (n + 1)).comp
          (relativePositiveBarWordMap k A I V n)) := by
  unfold barWordFiltration
  rw [coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting V]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. For c : Fin (n + 1) → Bool,
barStageToSplitWord p n c maps B_p to V ⊗[k] W_c by (id_V ⊗ P_c) ∘ W_n^V. -/
def barStageToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool) :
    barWordFiltration k A I V p n →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  (coefficientSplitAmbientToWord k A I V splitting colour).comp
    ((relativePositiveBarWordMap k A I V n).comp (barWordFiltration k A I V p n).subtype)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. If p < quotientEntryCount
c, barStageToSplitWord p n c x = 0 for every x : B_p. -/
theorem barStageToSplitWord_zero_of_quotient_count (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (h : p < quotientEntryCount colour)
    (x : barWordFiltration k A I V p n) :
    barStageToSplitWord k A I splitting V p n colour x = 0 := by
  have hc := splitWordPositionCounts_add colour
  have hrequired : splitWordIdealPositionCount colour < n + 1 - p := by omega
  have hxw : relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x) ∈
      coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p) := Submodule.mem_comap.mp x.property
  change coefficientSplitAmbientToWord k A I V splitting colour
    (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
  exact coefficientIdealWordSpan_le_ker_splitAmbientToWord k A I splitting V colour
    (n + 1 - p) hrequired hxw

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. For x : B_p, ∑ c, (id_V ⊗
J_c)(barStageToSplitWord p n c x) = W_n^V(x.val). -/
theorem barStage_splitWord_reconstruct (p n : ℕ)
    (x : barWordFiltration k A I V p n) :
    (∑ colour : Fin (n + 1) → Bool,
      coefficientSplitWordToAmbient k A I V splitting colour
        (barStageToSplitWord k A I splitting V p n colour x)) =
      relativePositiveBarWordMap k A I V n x.val :=
  coefficientSplitWord_reconstruct k A I V splitting
    (relativePositiveBarWordMap k A I V n x.val)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. If c has quotient count p,
the predecessor B_lower inside B_p lies in ker(barStageToSplitWord p n c). B_lower is zero at
p = 0 and B_(p−1) otherwise. -/
theorem barLowerFiltration_le_ker_stageToSplitWord (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (hcolour : quotientEntryCount colour = p) :
    (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype ≤
      LinearMap.ker (barStageToSplitWord k A I splitting V p n colour) := by
  intro x hx
  change barStageToSplitWord k A I splitting V p n colour x = 0
  have hxl : (barWordFiltration k A I V p n).subtype x ∈
      barLowerFiltration k A I V p n := Submodule.mem_comap.mp hx
  by_cases hp : p = 0
  · rw [barLowerFiltration, ite_eq_left hp] at hxl
    have hx0 : (barWordFiltration k A I V p n).subtype x = 0 := by
      simpa only [Submodule.mem_bot] using hxl
    change coefficientSplitAmbientToWord k A I V splitting colour
      (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
    rw [hx0, map_zero, map_zero]
  · rw [barLowerFiltration, ite_eq_right hp] at hxl
    have hxw : relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x) ∈
        coefficientIdealWordSpan k A I V (n + 1) (n + 1 - (p - 1)) := Submodule.mem_comap.mp hxl
    have hc := splitWordPositionCounts_add colour
    have hrequired : splitWordIdealPositionCount colour < n + 1 - (p - 1) := by omega
    change coefficientSplitAmbientToWord k A I V splitting colour
      (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
    exact coefficientIdealWordSpan_le_ker_splitAmbientToWord k A I splitting V colour
      (n + 1 - (p - 1)) hrequired hxw

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. For c with quotient count
p, barLayerToSplitWord maps barWordLayer p n = B_p/B_lower to V ⊗[k] W_c, induced by the stage
coordinate. -/
def barLayerToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) :
    barWordLayer k A I V p n →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  ((barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype).liftQ
    (barStageToSplitWord k A I splitting V p n colour)
    (barLowerFiltration_le_ker_stageToSplitWord k A I splitting V p n colour hcolour)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. For c with quotient count p
and x : B_p, barLayerToSplitWord c ([x]) = (id_V ⊗ P_c)(W_n^V(x.val)). -/
theorem barLayerToSplitWord_projection (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) (x : barWordFiltration k A I V p n) :
    barLayerToSplitWord k A I splitting V p n colour hcolour
        (barWordLayerProjection k A I V p n x) =
      coefficientSplitAmbientToWord k A I V splitting colour
        (relativePositiveBarWordMap k A I V n x.val) := rfl

/-- Let k be commutative, I a nonunital k-subalgebra of A, V a k-module and W_c its ideal/quotient
tensor word. barSplitWordGradeCoordinates p n is Π c : splitWordGradeColours p (n + 1), V ⊗[k]
W_c. -/
abbrev barSplitWordGradeCoordinates (p n : ℕ) : Type (max u v w) :=
  ∀ colour : splitWordGradeColours p (n + 1), V ⊗[k] splitWordTensor k A I colour.val

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map.
barLayerToSplitWordCoordinates maps barWordLayer p n to barSplitWordGradeCoordinates p n by
collecting the descended maps for all colours with quotient count p. -/
def barLayerToSplitWordCoordinates (p n : ℕ) :
    barWordLayer k A I V p n →ₗ[k] barSplitWordGradeCoordinates k A I V p n :=
  LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    barLayerToSplitWord k A I splitting V p n colour.val colour.property)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. barAssociatedSplitWordMap p
n is the degreewise module morphism from (barAssociatedWordComplex p).X (n + 1) to
ModuleCat.of k (barSplitWordGradeCoordinates p n), using the full descended coordinate family. -/
def barAssociatedSplitWordMap (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).X (n + 1) ⟶
      ModuleCat.of k (barSplitWordGradeCoordinates k A I V p n) :=
  ModuleCat.ofHom (barLayerToSplitWordCoordinates k A I splitting V p n)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Let V be any k-module. Put K_+ = ker(positiveBar(A,V) → positiveBar(A/I,V)), with
word map W_n^V in degree n + 1, and let B_p require n + 1 − p ideal entries. For a colour c,
let W_c tensor I at false positions and A/I at true positions; let J_c tensor inclusion or
section and P_c tensor the split ideal projection or quotient map. For x : B_p and c with
quotient count p, the c-coordinate of barLayerToSplitWordCoordinates([x]) equals (id_V ⊗
P_c)(W_n^V(x.val)). -/
theorem barLayerToSplitWordCoordinates_projection (p n : ℕ)
    (x : barWordFiltration k A I V p n) (colour : splitWordGradeColours p (n + 1)) :
    barLayerToSplitWordCoordinates k A I splitting V p n
        (barWordLayerProjection k A I V p n x) colour =
      coefficientSplitAmbientToWord k A I V splitting colour.val
        (relativePositiveBarWordMap k A I V n x.val) := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
