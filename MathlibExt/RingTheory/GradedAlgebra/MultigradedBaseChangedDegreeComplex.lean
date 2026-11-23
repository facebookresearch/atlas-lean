/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti
import MathlibExt.RingTheory.GradedAlgebra.MultigradedBaseChangedDifferential
import MathlibExt.RingTheory.GradedAlgebra.MultigradedBaseChangedTermDecomposition
import MathlibExt.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreePieceFinite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Degree components of the base-changed multigraded resolution

This file provides the degree-`α` complex of the base-changed multigraded
free resolution, its inclusion into the base-changed complex, the
inclusion's componentwise injectivity and range, and the assembly of the
repository's `MultigradedBaseChange` package from these pieces.

Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.
-/

public section

namespace MetaMathlibExt

universe u

/-- **Multidegree component complex of the base-changed resolution.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$. Write $K \otimes_R F$ for the chain complex of $K$-vector spaces obtained
from $F$ by extending scalars along the evaluation $R \to K$ at $x = 0$, and for
$\alpha \in \mathbb{Z}^n$ call the $K$-span of the vectors $1 \otimes e_j$ with $e_j$ of degree
$\alpha$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$. The degree-$\alpha$ complex is the
chain complex of $K$-vector spaces whose term in homological degree $i$ is the degree-$\alpha$
piece of $(K \otimes_R F)_i$ and whose differentials are the restrictions of the differentials
of $K \otimes_R F$.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeComplex`.

Source:
Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of
Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`. -/
public noncomputable def MultigradedFreeResolution.baseChangedDegreeComplex
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) :
    HomologicalComplex (ModuleCat.{u} K) (ComplexShape.down Nat) :=
  ChainComplex.of
    (fun i => ModuleCat.of K
      ↥(baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
        resolution ι res i α))
    (fun i => ModuleCat.ofHom (LinearMap.restrict
      (ModuleCat.Hom.hom ((baseChangedComplex resolution).d (i + 1) i))
      (fun x hx =>
        MultigradedFreeResolution.baseChangedDifferential_preservesDegree
          targetGraded resolution ι res i α x hx)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hbase := (baseChangedComplex resolution).d_comp_d (n + 1 + 1) (n + 1) n
      have hhom : ((baseChangedComplex resolution).d (n + 1) n).hom.comp
          ((baseChangedComplex resolution).d (n + 1 + 1) (n + 1)).hom = 0 := by
        rw [← ModuleCat.hom_comp, hbase, ModuleCat.hom_zero]
      have happ := LinearMap.congr_fun hhom ↑x
      simpa using happ)

/-- **Inclusion of a multidegree component complex.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$. Write $K \otimes_R F$ for the chain complex of $K$-vector spaces obtained
from $F$ by extending scalars along the evaluation $R \to K$ at $x = 0$, and for
$\alpha \in \mathbb{Z}^n$ call the $K$-span of the vectors $1 \otimes e_j$ with $e_j$ of degree
$\alpha$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$. The inclusion of the degree-$\alpha$
complex is the chain map from the degree-$\alpha$ complex of $K \otimes_R F$ to $K \otimes_R F$
whose component in each homological degree $i$ is the inclusion of the degree-$\alpha$ piece of
$(K \otimes_R F)_i$ into $(K \otimes_R F)_i$.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion`.

Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`. -/
public noncomputable def MultigradedFreeResolution.baseChangedDegreeInclusion
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) :
    HomologicalComplex.Hom
      (MultigradedFreeResolution.baseChangedDegreeComplex K n M
        targetGraded resolution ι res α)
      (baseChangedComplex (K := K) (n := n) (M := M) resolution) :=
  ChainComplex.ofHom
    (fun i => by
      letI := ModuleCat.isAddCommGroup ((baseChangedComplex resolution).X i)
      letI := ModuleCat.isModule ((baseChangedComplex resolution).X i)
      exact (ModuleCat.ofHom (Submodule.subtype
        (baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
          resolution ι res i α)) :
        ModuleCat.of K
          ↥(baseChangedDegreePiece (K := K) (n := n) (M := M) targetGraded
            resolution ι res i α) ⟶
          ModuleCat.of K ↥((baseChangedComplex resolution).X i)))
    (fun i => by
      simp only [MultigradedFreeResolution.baseChangedDegreeComplex,
        ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp)

/-- Each component of the degree inclusion is injective. Source:
Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of
Integer Sequences 23 (2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion_injective`. -/
public theorem
    MultigradedFreeResolution.baseChangedDegreeInclusion_injective
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) (i : Nat) :
    Function.Injective ⇑(ModuleCat.Hom.hom
      ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
        targetGraded resolution ι res α).f i)) :=
  Submodule.injective_subtype _

/-- Each component of the degree inclusion has range exactly the
degree piece `baseChangedDegreePiece`. Source: Benjamin Braun and
Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23
(2020), lines 864–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreeInclusion_range`. -/
public theorem
    MultigradedFreeResolution.baseChangedDegreeInclusion_range
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) (i : Nat) :
    LinearMap.range (ModuleCat.Hom.hom
      ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
        targetGraded resolution ι res α).f i)) =
      baseChangedDegreePiece (K := K) (n := n) (M := M)
        targetGraded resolution ι res i α :=
  Submodule.range_subtype _

/-- Homology of a chain complex of `K`-vector spaces is finite-dimensional
whenever the ambient term is: cycles embed into the term (Noetherian) and
homology is a quotient of cycles. -/
private theorem mbc_finite_homology (K : Type u) [Field K]
    (C : HomologicalComplex (ModuleCat.{u, u} K) (ComplexShape.down Nat))
    (i : Nat) [HomologicalComplex.HasHomology C i]
    (hfin : Module.Finite K ↥(C.X i)) :
    Module.Finite K ↥(HomologicalComplex.homology C i) := by
  have := hfin
  have : IsNoetherian K ↥(C.X i) :=
    isNoetherian_of_isNoetherianRing_of_finite K ↥(C.X i)
  have hinj : Function.Injective ((C.iCycles i).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hfin_cyc : Module.Finite K ↥(C.cycles i) :=
    Module.Finite.of_injective (C.iCycles i).hom hinj
  have := hfin_cyc
  have hsurj : Function.Surjective ((C.homologyπ i).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (C.homologyπ i).hom hsurj

/-- **Existence of multigraded base-change data.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$, where every index set $\iota_i$ is finite. Write $K \otimes_R F$ for the
chain complex of $K$-vector spaces obtained from $F$ by extending scalars along the evaluation
$R \to K$ at $x = 0$, and for $\alpha \in \mathbb{Z}^n$ call the $K$-span of the vectors
$1 \otimes e_j$ with $e_j$ of degree $\alpha$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$.
Then multigraded base-change data for $F$ exist: each $(K \otimes_R F)_i$ is the direct sum of
its degree-$\alpha$ pieces over $\alpha \in \mathbb{Z}^n$, the differentials of $K \otimes_R F$
preserve these pieces, and for every $\alpha$ there is a chain complex $C^\alpha$ of $K$-vector
spaces with finite-dimensional homology in every degree, together with a chain map
$C^\alpha \to K \otimes_R F$ that is injective in each homological degree $i$ with image the
degree-$\alpha$ piece of $(K \otimes_R F)_i$.

Proves `Wanted` entry `MultigradedFreeResolution.multigradedBaseChange_nonempty`.

Source: Benjamin Braun and Brian Davis, "Antichain Simplices," Journal of
Integer Sequences 23 (2020), lines 862–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`. -/
public theorem MultigradedFreeResolution.multigradedBaseChange_nonempty
    {K : Type u} [Field K]
    {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (finiteBasis : ∀ i, Finite (ι i)) :
    Nonempty (MultigradedBaseChange targetGraded resolution ι res) := by
  refine ⟨{
    decomposition :=
      MultigradedFreeResolution.baseChangedDegreeDecomposition targetGraded
        resolution ι res,
    diffPreserves :=
      MultigradedFreeResolution.baseChangedDifferential_preservesDegree
        targetGraded resolution ι res,
    comp := MultigradedFreeResolution.baseChangedDegreeComplex K n M
      targetGraded resolution ι res,
    incl := MultigradedFreeResolution.baseChangedDegreeInclusion K n M
      targetGraded resolution ι res,
    incl_injective :=
      MultigradedFreeResolution.baseChangedDegreeInclusion_injective K n M
        targetGraded resolution ι res,
    range_eq := MultigradedFreeResolution.baseChangedDegreeInclusion_range K n M
      targetGraded resolution ι res,
    hasHom := fun α i => inferInstance,
    finiteDim := by
      intro α i _
      have := finiteBasis i
      exact mbc_finite_homology K _ i
        (MultigradedFreeResolution.baseChangedDegreePiece_finite K n M
          targetGraded resolution ι res α i) }⟩

end MetaMathlibExt
