/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti

@[expose] public section

namespace MetaMathlibExt

universe u

/-- **Multidegree decomposition of the base-changed resolution.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$. Write $K \otimes_R F$ for the chain complex of $K$-vector spaces obtained
from $F$ by extending scalars along the evaluation $R \to K$ at $x = 0$, and for
$\alpha \in \mathbb{Z}^n$ call the $K$-span of the vectors $1 \otimes e_j$ with $e_j$ of degree
$\alpha$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$. For every $i \ge 0$, this is the
decomposition of $(K \otimes_R F)_i$ as the internal direct sum of its degree-$\alpha$ pieces
over $\alpha \in \mathbb{Z}^n$.

Source: Braun-Davis, JIS 23 (2020), lines 856-867.
See https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex -/
@[instance_reducible]
public noncomputable def MultigradedFreeResolution.baseChangedDegreeDecomposition
    {K : Type u} [Field K] {n : ℕ} {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u) (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) :
    DirectSum.Decomposition
      (fun α => baseChangedDegreePiece targetGraded resolution ι res i α) := by
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  letI : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  let b : Module.Basis (ι i) K ↥((baseChangedComplex resolution).X i) :=
    (res.termFree i).basis.baseChange K
  have fiberEq : ∀ a : (Fin n →₀ Int),
      ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
        Set ↥((baseChangedComplex resolution).X i)) =
      ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
        Set ↥((baseChangedComplex resolution).X i)) := by
    intro a
    apply Set.ext
    intro y
    constructor
    · intro hy
      obtain ⟨j, hjDeg, rfl⟩ := hy
      exact ⟨j, hjDeg, rfl⟩
    · intro hy
      change ∃ j : ι i, j ∈ ({ k : ι i | (res.termFree i).degree k = a } :
        Set (ι i)) ∧ b j = y at hy
      obtain ⟨j, hjMem, rfl⟩ := hy
      exact ⟨j, hjMem, rfl⟩
  have basisInd : LinearIndependent K (⇑b) := b.linearIndependent
  have hiSpan : iSupIndep (fun a : (Fin n →₀ Int) =>
      Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i))) := by
    intro a
    change Disjoint
      (Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i)))
      (⨆ c : (Fin n →₀ Int), ⨆ _ : c ≠ a, Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = c ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i)))
    have hDisjIdx : Disjoint
        ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))
        (⋃ c : (Fin n →₀ Int), ⋃ _ : c ≠ a,
          ({ k : ι i | (res.termFree i).degree k = c } : Set (ι i))) := by
      rw [Set.disjoint_left]
      intro j hjA hjRest
      rw [Set.mem_iUnion] at hjRest
      obtain ⟨c, hcRest⟩ := hjRest
      rw [Set.mem_iUnion] at hcRest
      obtain ⟨hNe, hjC⟩ := hcRest
      have hjA' : (res.termFree i).degree j = a := hjA
      have hjC' : (res.termFree i).degree j = c := hjC
      exact hNe (hjC'.symm.trans hjA')
    have hDisjSpan : Disjoint
        (Submodule.span K
          ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
            Set ↥((baseChangedComplex resolution).X i)))
        (Submodule.span K
          ((⇑b '' (⋃ c : (Fin n →₀ Int), ⋃ _ : c ≠ a,
            ({ k : ι i | (res.termFree i).degree k = c } : Set (ι i)))) :
            Set ↥((baseChangedComplex resolution).X i))) :=
      basisInd.disjoint_span_image hDisjIdx
    have hFA : Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i)) =
        Submodule.span K
          ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
            Set ↥((baseChangedComplex resolution).X i)) := by
      rw [fiberEq a]
    rw [hFA]
    refine Disjoint.mono_right ?_ hDisjSpan
    apply iSup_le
    intro c
    apply iSup_le
    intro hc
    have hNe : c ≠ a := hc
    rw [fiberEq c]
    apply Submodule.span_mono
    apply Set.image_mono
    intro j hj
    rw [Set.mem_iUnion]
    refine ⟨c, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hNe, hj⟩
  have hsSpan : (⨆ a : (Fin n →₀ Int), Submodule.span K
      ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
        Set ↥((baseChangedComplex resolution).X i))) = ⊤ := by
    have coverEq : (⋃ a : (Fin n →₀ Int),
        ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
          Set ↥((baseChangedComplex resolution).X i))) =
        Set.range (⇑b) := by
      apply Set.ext
      intro y
      constructor
      · intro hy
        rw [Set.mem_iUnion] at hy
        obtain ⟨a, ha⟩ := hy
        change ∃ j : ι i, j ∈ ({ k : ι i | (res.termFree i).degree k = a } :
          Set (ι i)) ∧ b j = y at ha
        obtain ⟨j, hjMem, hjEq⟩ := ha
        exact Set.mem_range.mpr ⟨j, hjEq⟩
      · intro hy
        obtain ⟨j, hjEq⟩ := Set.mem_range.mp hy
        rw [Set.mem_iUnion]
        exact ⟨(res.termFree i).degree j, j, rfl, hjEq⟩
    calc (⨆ a : (Fin n →₀ Int), Submodule.span K
            ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
              Set ↥((baseChangedComplex resolution).X i)))
        = (⨆ a : (Fin n →₀ Int), Submodule.span K
            ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
              Set ↥((baseChangedComplex resolution).X i))) := by
          simp only [fiberEq]
      _ = Submodule.span K
            (⋃ a : (Fin n →₀ Int),
              ((⇑b '' ({ k : ι i | (res.termFree i).degree k = a } : Set (ι i))) :
                Set ↥((baseChangedComplex resolution).X i))) :=
          (Submodule.span_iUnion _).symm
      _ = Submodule.span K (Set.range (⇑b)) := by
          rw [coverEq]
      _ = ⊤ := b.span_eq
  have hIntSpan : DirectSum.IsInternal (fun a : (Fin n →₀ Int) =>
      Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i))) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hiSpan hsSpan
  have familyEq : (fun α : (Fin n →₀ Int) =>
        baseChangedDegreePiece targetGraded resolution ι res i α) =
      (fun a : (Fin n →₀ Int) => Submodule.span K
        ({ y | ∃ j : ι i, (res.termFree i).degree j = a ∧ y = b j } :
          Set ↥((baseChangedComplex resolution).X i))) :=
    funext (fun α => rfl)
  have hInt : DirectSum.IsInternal (fun α : (Fin n →₀ Int) =>
      baseChangedDegreePiece targetGraded resolution ι res i α) := by
    rw [familyEq]
    exact hIntSpan
  exact DirectSum.IsInternal.chooseDecomposition _ hInt

end MetaMathlibExt
