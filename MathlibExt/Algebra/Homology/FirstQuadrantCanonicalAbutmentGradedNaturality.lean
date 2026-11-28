/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentImageQuotientNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentPreviousImageNaturality

/-!
# Naturality of the canonical abutment associated-graded comparison

Let K be a bicomplex of shape (down ℕ,down ℕ) in an abelian category. For p,q∈ℕ set m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Write a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u)
for the complete-filtration relative homology maps. The inclusion image(a_K≫b_K)→image b_K has
cokernel Q_K, the nested-image quotient presenting the canonical abutment term E_K at cuts
⊥≤ℓ≤p≤u and degree -m.

The previous and current image comparisons identify this inclusion with F_{p-1}H_m(Tot
K)→F_pH_m(Tot K). Its cokernel is the associated-graded piece gr_pH_m(Tot K). Bicomplex
morphisms induce compatible maps on the two images, their cokernels and E_K. The resulting
isomorphisms Q_K≅gr_pH_m(Tot K) and E_K≅gr_pH_m(Tot K) are natural, with arbitrary category
universes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let f:K→L be a morphism of first-quadrant bicomplexes in an abelian category and p,q∈ℕ. Set
m=p+q, ℓ=(p:ℤ)−1 and u=m+1. For the relative homology arrows a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and
b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), write j_K:image(a_K≫b_K)→image b_K for the nested-image
inclusion. This arrow-category morphism j_K→j_L has left edge the previous image map J_f and
right edge the current image map I_f; it satisfies J_f≫j_L=j_K≫I_f. -/
noncomputable def horizontalCanonicalAbutmentImageCompSquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (CategoryTheory.imageCompMap
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ⟶
      Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) :=
  Arrow.homMk
    (horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q)
    (horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q)
    (by
      apply (cancel_mono (image.ι
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q))).1
      calc
        (horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) ≫
              image.ι (horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
          horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap L p q) ≫
                image.ι
                  (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) :=
            Category.assoc _ _ _
        _ = horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            image.ι (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
              horizontalCanonicalAbutmentToUpperHomologyMap L p q) := by
          rw [CategoryTheory.imageCompMap_ι]
        _ = image.ι
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
                horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            ((horizontalCompleteFiltrationSpectralObjectMap f).hom
              (-((p + q : ℕ) : ℤ))).app
                (ComposableArrows.mk₁
                  (horizontalCanonicalAbutmentTotalMap p q)) := by
          rw [horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι]
        _ = (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
                image.ι
                  (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≫
            ((horizontalCompleteFiltrationSpectralObjectMap f).hom
              (-((p + q : ℕ) : ℤ))).app
                (ComposableArrows.mk₁
                  (horizontalCanonicalAbutmentTotalMap p q)) := by
          rw [CategoryTheory.imageCompMap_ι]
        _ = CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            (image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
              ((horizontalCompleteFiltrationSpectralObjectMap f).hom
                (-((p + q : ℕ) : ℤ))).app
                  (ComposableArrows.mk₁
                    (horizontalCanonicalAbutmentTotalMap p q))) :=
          Category.assoc _ _ _
        _ = CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            (horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
              image.ι
                (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) := by
          rw [horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι]
        _ = (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q) ≫
              image.ι
                (horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
          (Category.assoc _ _ _).symm)

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p), b:H^{-m}(⊥,p)→H^{-m}(⊥,u),
j:image(a≫b)→image b and Q=coker j. The induced map Q_K→Q_L equals the cokernel-functor image of
the natural square between j_K and j_L whose edges are the previous and current image maps of f. -/
@[simp]
theorem horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q =
      (Limits.coker C).map
        (horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q) := by
  let sq := horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q
  apply (cancel_epi (cokernel.π (CategoryTheory.imageCompMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)))).1
  rw [horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π]
  exact (Limits.coker.π C).naturality sq

/-- Let f:K→L be a morphism of first-quadrant bicomplexes in an abelian category and p,q∈ℕ. Set
m=p+q, ℓ=(p:ℤ)−1 and u=m+1. For a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and
b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), let Q_K=coker(image(a_K≫b_K)→image b_K). The previous and
current image comparisons give e_K:Q_K≅gr_pH_m(Tot K), where gr_p is the cokernel of
F_{p-1}→F_p. With Q_f the induced quotient map and gr_pH_m(Tot f) the induced graded map,
Q_f≫e_L.hom=e_K.hom≫gr_pH_m(Tot f). -/
theorem horizontalCanonicalAbutmentImageQuotientGradedIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom =
      (horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  let sourceSquare :=
    horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q
  let targetSquare :=
    horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q
  let eK : Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≅
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) :=
    Arrow.isoMk'
      (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q))
      (horizontalTotalHomologyFiltrationStepMap K p q)
      (horizontalCanonicalAbutmentPreviousImageIso K p q)
      (horizontalCanonicalAbutmentCurrentImageIso K p q)
      (horizontalCanonicalAbutmentImageSquare K p q).symm
  let eL : Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) ≅
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap L p q) :=
    Arrow.isoMk'
      (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q))
      (horizontalTotalHomologyFiltrationStepMap L p q)
      (horizontalCanonicalAbutmentPreviousImageIso L p q)
      (horizontalCanonicalAbutmentCurrentImageIso L p q)
      (horizontalCanonicalAbutmentImageSquare L p q).symm
  have hArrow : sourceSquare ≫ eL.hom = eK.hom ≫ targetSquare := by
    apply Arrow.hom_ext
    · exact horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
        f p q
    · exact horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
        f p q
  rw [horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map]
  change (Limits.coker C).map sourceSquare ≫
      ((Limits.coker C).mapIso eL).hom =
    ((Limits.coker C).mapIso eK).hom ≫
      (Limits.coker C).map targetSquare
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k => (Limits.coker C).map k) hArrow

/-- For a morphism f:K→L of bicomplexes of shape (down ℕ,down ℕ) in an abelian category and p,q∈ℕ,
put m=p+q, ℓ=(p:ℤ)−1 and u=m+1. Let E_K be the canonical spectral abutment term at cuts ⊥≤ℓ≤p≤u
in degree -m, and gr_pH_m(Tot K)=coker(F_{p-1}→F_p) the horizontal homology graded piece. The
cokernel and nested-image comparisons yield e_K:E_K≅gr_pH_m(Tot K). The canonical spectral E-map
E_f and the total-homology graded map satisfy E_f≫e_L.hom=e_K.hom≫gr_pH_m(Tot f). -/
theorem horizontalCanonicalAbutmentGradedIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentGradedIso L p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  have hImageQuotient :=
    horizontalCanonicalAbutmentImageQuotientIso_naturality f p q
  have hGraded :=
    horizontalCanonicalAbutmentImageQuotientGradedIso_naturality f p q
  dsimp only [horizontalCanonicalAbutmentGradedIso, Iso.trans_hom]
  calc
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          ((horizontalCanonicalAbutmentImageQuotientIso L p q).hom ≫
            (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom) =
        (horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentImageQuotientIso L p q).hom) ≫
            (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom :=
      (Category.assoc _ _ _).symm
    _ = ((horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
          horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q) ≫
        (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom := by
      rw [hImageQuotient]
    _ = (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        (horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom) :=
      Category.assoc _ _ _
    _ = (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        ((horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom ≫
          horizontalTotalHomologyGradedPieceMapOfBicomplex f p q) := by
      rw [hGraded]
    _ = ((horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
          (horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom) ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
