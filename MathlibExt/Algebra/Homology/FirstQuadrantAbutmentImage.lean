/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantStablePage
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotient

/-!
# Finite abutment as a quotient of nested stage images

Let C be an abelian category and K a bicomplex indexed by two down ℕ shapes. Its complete
horizontal filtration gives a cochain spectral object indexed by EInt. For p,q : ℕ put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Denote relative cochain homology from cut s to cut t by Hᵃ(s,t).

The stages at bottom ⊥ and finite cut -1 are zero, so the finite abutment with lower cut -1 is
canonically identified with the bottom-indexed E-object for ⊥≤ℓ≤p≤u, in degrees -m-1,-m,-m+1.
For r≥1, r≥p+1 and r≥q+2, the page-r term at (p,q) is this canonical abutment term.

The two incoming maps are a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and δ:H^{-m-1}(p,u)→H^{-m}(⊥,p). Exactness
of δ followed by the upper-stage map b identifies coker[a,δ] with image b modulo image(a≫b),
both images inside H^{-m}(⊥,u). The object and morphism universes of C are arbitrary.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- For p,q : ℕ, let ℓ=(p:ℤ)−1 and u=(p+q+1:ℤ), viewed as finite EInt cuts. Then ⊥≤ℓ and the finite
cut p≤u. These inequalities locate the consecutive column cuts ℓ≤p between bottom and the upper
abutment stage. -/
theorem horizontalCanonicalAbutmentIndices_le (p q : ℕ) :
    (⊥ : EInt) ≤ horizontalFirstPageLowerIndex p ∧
      horizontalFirstPageUpperIndex p ≤ horizontalAbutmentUpperIndex p q :=
  ⟨bot_le, (horizontalAbutmentIndices_le p q).2⟩

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. horizontalFirstQuadrantCanonicalAbutmentTerm is the spectral E-object for
the cuts ⊥≤ℓ≤p≤u with consecutive cochain degrees -m-1,-m,-m+1. Its lower stage is the
bottom cut ⊥. -/
noncomputable abbrev horizontalFirstQuadrantCanonicalAbutmentTerm
    (p q : ℕ) : C :=
  let X := horizontalCompleteFiltrationSpectralObject K
  X.E
    (homOfLE (horizontalCanonicalAbutmentIndices_le p q).1)
    (homOfLE (horizontalFirstPageIndex_le p))
    (homOfLE (horizontalCanonicalAbutmentIndices_le p q).2)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. The cochain
diagram object F_⊥ is a zero complex, since the bottom complete filtered total complex is zero
and extension along the chain-to-cochain degree embedding preserves it. -/
theorem horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot :
    IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj (⊥ : EInt)) := by
  change IsZero ((ComplexShape.embeddingDownNat.extendFunctor C).obj
    (horizontalCompleteFilteredTotalComplex K (⊥ : EInt)))
  rw [horizontalCompleteFilteredTotalComplex_bot]
  exact (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
    HomologicalComplex.isZero_zero

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The object H^{-m+1}(⊥,-1) is zero: both the bottom stage and the finite
negative stage -1 of the complete cochain filtration are zero. -/
theorem horizontalBottomToNegativeRelativeHomologyIsZero (p q : ℕ) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ) + 1)).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ horizontalAbutmentLowerIndex
          from bot_le)))) := by
  apply horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero K
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
      (-1) (by omega)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The finite abutment term with lower cut -1 is canonically isomorphic to the
bottom-indexed canonical abutment term. The spectral transport uses H^{-m+1}(⊥,-1)=0 and the
consecutive degrees -m-1,-m,-m+1. -/
noncomputable def horizontalFiniteToCanonicalAbutmentIso (p q : ℕ) :
    horizontalFirstQuadrantAbutmentTerm K p q ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q := by
  let X : CategoryTheory.Abelian.SpectralObject C EInt :=
    horizontalCompleteFiltrationSpectralObject K
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := rfl
  exact (X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt)
    horizontalAbutmentLowerIndex
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalAbutmentUpperIndex p q)
    bot_le
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    n₀ n₁ n₂
    (horizontalBottomToNegativeRelativeHomologyIsZero K p q) hn₁ hn₂).symm

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. For r : ℤ satisfying 1≤r, p+1≤r and q+2≤r, the page-r object in bidegree
(p,q) of the horizontal first-quadrant spectral sequence is canonically isomorphic to the
bottom-indexed finite abutment term. -/
noncomputable def horizontalStablePageCanonicalAbutmentIso
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q :=
  horizontalStablePageAbutmentIso K r hr p q hlower hupper ≪≫
    horizontalFiniteToCanonicalAbutmentIso K p q

/-- For p : ℕ, horizontalCanonicalAbutmentLowerMap is the unique EInt order morphism ⊥→ℓ, with
ℓ=(p:ℤ)−1. -/
noncomputable abbrev horizontalCanonicalAbutmentLowerMap (p : ℕ) :
    (⊥ : EInt) ⟶ horizontalFirstPageLowerIndex p :=
  homOfLE bot_le

/-- For p : ℕ, horizontalCanonicalAbutmentMiddleMap is the EInt inclusion ℓ→p for ℓ=(p:ℤ)−1. In
particular the lower cut at p=0 is the integer -1. -/
noncomputable abbrev horizontalCanonicalAbutmentMiddleMap (p : ℕ) :
    horizontalFirstPageLowerIndex p ⟶ horizontalFirstPageUpperIndex p :=
  homOfLE (horizontalFirstPageIndex_le p)

/-- For p,q : ℕ, horizontalCanonicalAbutmentUpperMap is the EInt inclusion p→u with u=(p+q+1:ℤ). -/
noncomputable abbrev horizontalCanonicalAbutmentUpperMap (p q : ℕ) :
    horizontalFirstPageUpperIndex p ⟶ horizontalAbutmentUpperIndex p q :=
  homOfLE (horizontalAbutmentIndices_le p q).2

/-- For p : ℕ, horizontalCanonicalAbutmentLowerCompositeMap is the EInt order morphism ⊥→p, the
composite of ⊥→(p−1) and (p−1)→p. -/
noncomputable abbrev horizontalCanonicalAbutmentLowerCompositeMap (p : ℕ) :
    (⊥ : EInt) ⟶ horizontalFirstPageUpperIndex p :=
  homOfLE bot_le

/-- For p,q : ℕ, horizontalCanonicalAbutmentTotalMap is the EInt order morphism ⊥→u, with
u=(p+q+1:ℤ). -/
noncomputable abbrev horizontalCanonicalAbutmentTotalMap (p q : ℕ) :
    (⊥ : EInt) ⟶ horizontalAbutmentUpperIndex p q :=
  homOfLE bot_le

/-- For p : ℕ, composing horizontalCanonicalAbutmentLowerMap:⊥→p−1 with
horizontalCanonicalAbutmentMiddleMap:p−1→p gives
horizontalCanonicalAbutmentLowerCompositeMap:⊥→p. -/
theorem horizontalCanonicalAbutmentLower_comp_middle (p : ℕ) :
    horizontalCanonicalAbutmentLowerMap p ≫
        horizontalCanonicalAbutmentMiddleMap p =
      horizontalCanonicalAbutmentLowerCompositeMap p :=
  Subsingleton.elim _ _

/-- For p,q : ℕ, the composite ⊥→p→p+q+1 equals the EInt order map ⊥→p+q+1, using the canonical
abutment lower-composite and upper inclusions. -/
theorem horizontalCanonicalAbutmentLowerComposite_comp_upper
    (p q : ℕ) :
    horizontalCanonicalAbutmentLowerCompositeMap p ≫
        horizontalCanonicalAbutmentUpperMap p q =
      horizontalCanonicalAbutmentTotalMap p q :=
  Subsingleton.elim _ _

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The cut inclusion ℓ→p induces a map a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p), named
horizontalCanonicalAbutmentPreviousHomologyMap. -/
noncomputable abbrev horizontalCanonicalAbutmentPreviousHomologyMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentLowerMap p)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentLower_comp_middle p))

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The composition ⊥→p→u gives the connecting map δ:H^{-m-1}(p,u)→H^{-m}(⊥,p).
Thus the connecting map raises the cochain degree by one. -/
noncomputable abbrev horizontalCanonicalAbutmentBoundaryMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q + 1 : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentUpperMap p q)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) :=
  (horizontalCompleteFiltrationSpectralObject K).δ
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The inclusion p→u induces b:H^{-m}(⊥,p)→H^{-m}(⊥,u), named
horizontalCanonicalAbutmentToUpperHomologyMap. -/
noncomputable abbrev horizontalCanonicalAbutmentToUpperHomologyMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (horizontalCanonicalAbutmentTotalMap p q)
        (horizontalCanonicalAbutmentLowerComposite_comp_upper p q))

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. For δ:H^{-m-1}(p,u)→H^{-m}(⊥,p) and b:H^{-m}(⊥,p)→H^{-m}(⊥,u), the
composite δ≫b is zero. -/
theorem horizontalCanonicalAbutmentBoundary_comp_toUpper (p q : ℕ) :
    horizontalCanonicalAbutmentBoundaryMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q = 0 :=
  (horizontalCompleteFiltrationSpectralObject K).zero₁
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentTotalMap p q)
    (horizontalCanonicalAbutmentLowerComposite_comp_upper p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The sequence H^{-m-1}(p,u) —δ→ H^{-m}(⊥,p) —b→ H^{-m}(⊥,u) is exact at its
middle object, so image δ equals kernel b. -/
theorem horizontalCanonicalAbutmentBoundaryToUpper_exact (p q : ℕ) :
    (ShortComplex.mk
      (horizontalCanonicalAbutmentBoundaryMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)).Exact :=
  (horizontalCompleteFiltrationSpectralObject K).exact₁
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentTotalMap p q)
    (horizontalCanonicalAbutmentLowerComposite_comp_upper p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The spectral cokernel sequence has incoming arrow [a,δ] from
H^{-m}(⊥,ℓ)⊕H^{-m-1}(p,u) to H^{-m}(⊥,p), followed by the quotient map to the canonical abutment
E-object. -/
noncomputable abbrev horizontalCanonicalAbutmentCokernelSequence
    (p q : ℕ) : ShortComplex C :=
  (horizontalCompleteFiltrationSpectralObject K).cokernelSequenceE
    (horizontalCanonicalAbutmentLowerMap p)
    (horizontalCanonicalAbutmentMiddleMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentLower_comp_middle p)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The cokernel short complex with arrows [a,δ] and the canonical E-object
quotient map is exact at H^{-m}(⊥,p). Its incoming images impose the preceding-stage and
connecting-boundary relations. -/
theorem horizontalCanonicalAbutmentCokernelSequence_exact (p q : ℕ) :
    (horizontalCanonicalAbutmentCokernelSequence K p q).Exact :=
  (horizontalCompleteFiltrationSpectralObject K).cokernelSequenceE_exact
    (horizontalCanonicalAbutmentLowerMap p)
    (horizontalCanonicalAbutmentMiddleMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentLower_comp_middle p)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and δ:H^{-m-1}(p,u)→H^{-m}(⊥,p). Then
coker[a,δ] is canonically isomorphic to horizontalFirstQuadrantCanonicalAbutmentTerm K p q. -/
noncomputable def horizontalCanonicalAbutmentCokernelIso (p q : ℕ) :
    cokernel (biprod.desc
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)) ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q := by
  let S : ShortComplex C := horizontalCanonicalAbutmentCokernelSequence K p q
  have hS : S.Exact :=
    horizontalCanonicalAbutmentCokernelSequence_exact K p q
  letI : Epi S.g := by
    exact inferInstanceAs
      (Epi ((horizontalCompleteFiltrationSpectralObject K).cokernelSequenceE
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentLower_comp_middle p)
        (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
        (-((p + q : ℕ) : ℤ) + 1)).g)
  let canonical : CokernelCofork S.f := CokernelCofork.ofπ S.g S.zero
  let standard : CokernelCofork S.f :=
    CokernelCofork.ofπ (cokernel.π S.f) (cokernel.condition S.f)
  have hCanonical : IsColimit canonical := hS.gIsCokernel
  have hStandard : IsColimit standard := cokernelIsCokernel S.f
  exact IsColimit.coconePointUniqueUpToIso
    hStandard hCanonical

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. For a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and b:H^{-m}(⊥,p)→H^{-m}(⊥,u),
horizontalCanonicalAbutmentImageQuotient is coker(image(a≫b)→image b). Both images are taken in
H^{-m}(⊥,u). -/
noncomputable abbrev horizontalCanonicalAbutmentImageQuotient
    (p q : ℕ) : C :=
  cokernel (CategoryTheory.imageCompMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q))

/-- Let C be an abelian category in arbitrary object and morphism universes, K a bicomplex of shape
(down ℕ,down ℕ), and F its complete horizontal cochain filtration indexed by EInt. For p,q : ℕ
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Write Hᵃ(s,t) for the spectral object's relative cochain
homology of F_s→F_t. The canonical abutment term is isomorphic to image(H^{-m}(⊥,p)→H^{-m}(⊥,u))
modulo image(H^{-m}(⊥,ℓ)→H^{-m}(⊥,u)). The long homology sequence identifies the connecting
image with the upper-map kernel. -/
noncomputable def horizontalCanonicalAbutmentImageQuotientIso
    (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalCanonicalAbutmentImageQuotient K p q :=
  (horizontalCanonicalAbutmentCokernelIso K p q).symm ≪≫
    CategoryTheory.imageQuotientBiprodIso
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)
      (horizontalCanonicalAbutmentBoundaryToUpper_exact K p q)

end HomologicalComplex₂
