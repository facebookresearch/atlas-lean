/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionTotal

/-!
# Homology of complete-to-finite filtration diagram comparisons

Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. Fix
n∈ℕ. Pointwise H_n sends a natural-index diagram of chain complexes to a diagram in C. For a
first-quadrant bicomplex K, the restricted complete diagram i↦H_n(G_{e(i)}(K)), finite diagram
i↦H_n(G^fin_i(K)) and constant diagram i↦H_n(Tot K) are functorial in K, where e(i) is the
finite integer cut i.

The chain-stage comparisons ε_{K,i}:G_{e(i)}(K)≅G^fin_i(K) induce a natural isomorphism between
the first two homology diagrams. It is natural both in the filtration index i and in the
bicomplex K, and preserves their maps into the constant total-homology diagram. Componentwise,
H_n(ε_{K,i}.hom)≫H_n(ι^fin_i)=H_n(ι_{e(i)}). The object and morphism universes of C are
arbitrary.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C] [CategoryWithHomology C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
n∈ℕ, this functor sends a diagram D:ℕ→ChainComplex(C,ℕ) of shape down ℕ to the diagram
i↦H_n(D_i) in C. A transition i≤j is sent to H_n(D_{i→j}), and a natural transformation D→E is
sent to its degree-n homology map at every index. Homology degree n is fixed independently of
the filtration index i. -/
noncomputable abbrev horizontalNatDiagramHomologyFunctor (n : ℕ) :
    (ℕ ⥤ ChainComplex C ℕ) ⥤ (ℕ ⥤ C) :=
  (Functor.whiskeringRight ℕ (ChainComplex C ℕ) C).obj
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
fixed n∈ℕ, this functor sends a bicomplex K of shape (down ℕ,down ℕ) to the diagram
i↦H_n(G_{e(i)}(K)), where e(i) is the finite integer cut i in the complete horizontal
filtration. Diagram transitions are homology maps of complete-stage inclusions. A bicomplex
morphism f:K→L is sent at i to H_n(G_{e(i)}(f)). -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
    (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
fixed n∈ℕ, this functor sends a bicomplex K of shape (down ℕ,down ℕ) to the natural-index
diagram i↦H_n(G^fin_i(K)) of finite horizontal-stage homology. It sends each stage transition
i≤j to its homology map and each bicomplex morphism f:K→L to the natural transformation with
component H_n(G^fin_i(f)). -/
noncomputable def horizontalTotalFiltrationHomologyDiagramFunctor (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalTotalFiltrationDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
fixed n∈ℕ, this functor sends a first-quadrant bicomplex K to the constant natural-index diagram
with value H_n(Tot K). Every index transition acts as the identity, and a bicomplex morphism
f:K→L is sent to the transformation with component H_n(Tot f) at every index. -/
noncomputable def horizontalTotalHomologyNatConstDiagramFunctor (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalTotalComplexNatConstDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).obj K =
      (horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.obj K ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) :=
  rfl

@[simp]
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).obj K).obj i =
      (horizontalCompleteFilteredTotalComplex K
        ((i : ℤ) : EInt)).homology n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramFunctor n).obj K).obj i =
      (horizontalFilteredTotalComplex K i).homology n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalHomologyNatConstDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalHomologyNatConstDiagramFunctor n).obj K).obj i =
      (K.total (ComplexShape.down ℕ)).homology n :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).map f).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((i : ℤ) : EInt)) n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramFunctor n).map f).app i =
      HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexMapOfBicomplex f i) n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalHomologyNatConstDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalTotalHomologyNatConstDiagramFunctor n).map f).app i =
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n :=
  rfl

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. Fix
n∈ℕ. For a first-quadrant bicomplex K, let R_{K,n}(i)=H_n(G_{e(i)}(K)) and
S_{K,n}(i)=H_n(G^fin_i(K)), with e(i) the finite integer cut i. This isomorphism between the two
bicomplex-to-diagram functors has component H_n(ε_{K,i}):R_{K,n}(i)≅S_{K,n}(i), where ε_{K,i} is
the complete-to-finite stage comparison. It is natural in both K and i. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
    (n : ℕ) :
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
        (C := C) n ≅
      horizontalTotalFiltrationHomologyDiagramFunctor (C := C) n :=
  Functor.isoWhiskerRight
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
      (C := C) n).hom.app K).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexFiniteIso K
          (i : ℤ) (Int.natCast_nonneg i)).hom n :=
  rfl

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
fixed n∈ℕ, this natural transformation sends the finite-stage homology diagram
S_{K,n}(i)=H_n(G^fin_i(K)) to the constant diagram T_{K,n}(i)=H_n(Tot K), functorially in every
first-quadrant bicomplex K. Its component at K and i is H_n(ι^fin_i), induced by the canonical
finite-stage inclusion G^fin_i(K)→Tot K. -/
noncomputable def horizontalTotalFiltrationHomologyDiagramToTotal (n : ℕ) :
    horizontalTotalFiltrationHomologyDiagramFunctor (C := C) n ⟶
      horizontalTotalHomologyNatConstDiagramFunctor (C := C) n :=
  Functor.whiskerRight (horizontalTotalFiltrationDiagramToTotal (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramToTotal_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramToTotal
      (C := C) n).app K).app i =
      HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal K i) n :=
  rfl

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
fixed n∈ℕ, let R_{K,n}(i)=H_n(G_{e(i)}(K)), where K is a first-quadrant bicomplex and e(i) the
finite integer cut i. This bicomplex-natural transformation maps R_{K,n} to the constant diagram
with value H_n(Tot K); its component at K and i is H_n(ι_{e(i)}), the homology map of the
complete-stage inclusion. -/
noncomputable def
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
    (n : ℕ) :
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
        (C := C) n ⟶
      horizontalTotalHomologyNatConstDiagramFunctor (C := C) n :=
  Functor.whiskerRight
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

@[simp]
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
      (C := C) n).app K).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalToTotal K ((i : ℤ) : EInt)) n :=
  rfl

/-- Let C be preadditive with a zero object, finite coproducts and homology for chain complexes. For
n∈ℕ, write R_{K,n}(i)=H_n(G_{e(i)}(K)), S_{K,n}(i)=H_n(G^fin_i(K)), and T_{K,n}(i)=H_n(Tot K)
for first-quadrant bicomplexes K. Let ε_n:R_n≅S_n be the homology comparison, and s_n:S_n→T_n,
r_n:R_n→T_n the finite and complete inclusion transformations. Then ε_n.hom≫s_n=r_n as
transformations between bicomplex-to-diagram functors. At K and i this is
H_n(ε_{K,i}.hom)≫H_n(ι^fin_i)=H_n(ι_{e(i)}). -/
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal
    (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
        (C := C) n).hom ≫
        horizontalTotalFiltrationHomologyDiagramToTotal (C := C) n =
      horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
        (C := C) n := by
  change Functor.whiskerRight
          ((horizontalCompleteTotalFiltrationNatRestrictionNatIso
            (C := C)).hom)
          (horizontalNatDiagramHomologyFunctor (C := C) n) ≫
      Functor.whiskerRight (horizontalTotalFiltrationDiagramToTotal (C := C))
          (horizontalNatDiagramHomologyFunctor (C := C) n) =
    Functor.whiskerRight
      (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal (C := C))
      (horizontalNatDiagramHomologyFunctor (C := C) n)
  rw [← Functor.whiskerRight_comp]
  rw [horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal]

end HomologicalComplex₂

end
