/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Artinian
public import MathlibExt.Algebra.Homology.SequentialMilnor
public import MathlibExt.Algebra.Category.ModuleCat.MittagLefflerArtinian
public import MathlibExt.Algebra.Category.ModuleCat.SequentialMittagLeffler

/-!
# Artinian towers and Milnor edge isomorphisms

Let C be abelian with exact countable products and sequential inverse limits.
For a tower K with epic product difference Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁)
and c.Rel(i,j), vanishing of the concrete lim¹ of H_iK makes the Milnor
edge H_j(lim K) → lim(H_jK) an isomorphism, natural in towers and preserving
the homology maps of their stage projections.

For R-module complexes over an arbitrary ring, Artinian homology in degree i
gives the Mittag–Leffler condition and lim¹ vanishing. Artinian terms in that
single degree suffice because homology is a subquotient. If the terms are
Artinian in every degree, the product difference is also epic, giving the
edge isomorphism from the degreewise Artinian hypotheses alone.
The ring, module-carrier and complex-index universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace HomologicalComplex

section Vanishing

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and K an inverse tower of complexes.
Assume Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, c.Rel(i,j), and
lim¹(H_iK)=Coker(Δ_{H_iK}) is a zero object.

The canonical edge H_j(lim K) → lim(H_jK) is an isomorphism. -/
theorem isIso_sequentialMilnorEdge_of_isZero
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    IsIso (sequentialMilnorEdge K hK i j hij) := by
  have hS := sequentialMilnorShortComplex_shortExact K hK i j hij
  have hX : IsZero (sequentialMilnorShortComplex K hK i j hij).X₁ := by
    rw [sequentialMilnorShortComplex_X₁]
    exact h₁
  have h := (hS.isIso_g_iff).mpr hX
  simpa only [sequentialMilnorShortComplex_g, sequentialMilnorShortComplex_X₂,
    sequentialMilnorShortComplex_X₃] using h

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and K an inverse tower of complexes.
Assume Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, c.Rel(i,j), and
lim¹(H_iK)=Coker(Δ_{H_iK}) is a zero object.

The canonical isomorphism H_j(lim K) ≅ lim(H_jK) with the Milnor edge as forward map. -/
def sequentialMilnorIsoOfIsZero
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) := by
  have : IsIso (sequentialMilnorEdge K hK i j hij) :=
    isIso_sequentialMilnorEdge_of_isZero K hK i j hij h₁
  exact asIso (sequentialMilnorEdge K hK i j hij)

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and K an inverse tower of complexes.
Assume Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, c.Rel(i,j), and
lim¹(H_iK)=Coker(Δ_{H_iK}) is a zero object.

The forward map of the comparison H_j(lim K) ≅ lim(H_jK) equals the canonical Milnor edge. -/
@[simp]
theorem sequentialMilnorIsoOfIsZero_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).hom =
      sequentialMilnorEdge K hK i j hij := rfl

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and K an inverse tower of complexes.
Assume Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, c.Rel(i,j), and
lim¹(H_iK)=Coker(Δ_{H_iK}) is a zero object.

For every stage n, the forward comparison followed by lim(H_jK) → H_j(Kₙ) equals H_j of the stage projection lim K → Kₙ. -/
@[reassoc]
theorem sequentialMilnorIsoOfIsZero_hom_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) (n : ℕ) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).hom ≫
        limit.π (sequentialHomologyTower K j) (op n) =
      homologyMap (limit.π K (op n)) j := by
  simpa only [sequentialMilnorIsoOfIsZero_hom] using
    sequentialMilnorEdge_π K hK i j hij n

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and K an inverse tower of complexes.
Assume Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, c.Rel(i,j), and
lim¹(H_iK)=Coker(Δ_{H_iK}) is a zero object.

For every stage n, H_j(lim K → Kₙ) composed after the inverse comparison equals the stage projection lim(H_jK) → H_j(Kₙ). -/
@[reassoc (attr := simp)]
theorem sequentialMilnorIsoOfIsZero_inv_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) (n : ℕ) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).inv ≫
        homologyMap (limit.π K (op n)) j =
      limit.π (sequentialHomologyTower K j) (op n) := by
  exact (congrArg (fun f : (limit K).homology j ⟶ (K.obj (op n)).homology j =>
      (sequentialMilnorIsoOfIsZero K hK i j hij h₁).inv ≫ f)
    (sequentialMilnorIsoOfIsZero_hom_π K hK i j hij h₁ n).symm).trans
      (Iso.inv_hom_id_assoc (sequentialMilnorIsoOfIsZero K hK i j hij h₁)
        (limit.π (sequentialHomologyTower K j) (op n)))

/-- Let C be abelian with exact countable products and sequential limits,
and α:K → L a map of towers of complexes of shape c. Suppose both
product differences are epic, c.Rel(i,j), and lim¹(H_iK),lim¹(H_iL)
are zero objects. Their comparisons ε_K,ε_L satisfy
ε_L ∘ H_j(lim α)=lim(H_jα) ∘ ε_K. -/
@[reassoc]
theorem sequentialMilnorIsoOfIsZero_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K)) (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j)
    (hK₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i)))
    (hL₁ : IsZero (sequentialLimOne (sequentialHomologyTower L i))) :
    homologyMap (limMap α) j ≫
        (sequentialMilnorIsoOfIsZero L hL i j hij hL₁).hom =
      (sequentialMilnorIsoOfIsZero K hK i j hij hK₁).hom ≫
        limMap (sequentialHomologyTowerMap α j) := by
  simpa only [sequentialMilnorIsoOfIsZero_hom] using
    sequentialMilnorEdge_naturality hK hL α i j hij

end Vanishing

section Modules

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}

/-- Let R be an arbitrary ring and K an inverse tower of R-module complexes
of any shape c. If each stage term Kₙᵢ is Artinian, then the tower of
degree-i terms is Mittag–Leffler: its later-stage images in each fixed
stage eventually stabilize. -/
theorem isMittagLeffler_sequentialDegreeTower_of_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    (sequentialDegreeTower K i).IsSequentialMittagLeffler := by
  apply ModuleCat.isMittagLeffler_of_isArtinian
  rintro ⟨n⟩
  exact h n

/-- Let R be an arbitrary ring and K an inverse tower of R-module complexes
of any shape c. If H_i(Kₙ) is Artinian at every stage n, its inverse
homology tower H_iK is Mittag–Leffler. -/
theorem isMittagLeffler_sequentialHomologyTower_of_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (sequentialHomologyTower K i).IsSequentialMittagLeffler := by
  apply ModuleCat.isMittagLeffler_of_isArtinian
  rintro ⟨n⟩
  exact h n

/-- Let R be an arbitrary ring and K an inverse tower of R-module complexes
of any shape c. If Kₙᵢ is Artinian for each stage n, then its subquotient
H_i(Kₙ) is Artinian and the homology tower H_iK is Mittag–Leffler. -/
theorem isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    (sequentialHomologyTower K i).IsSequentialMittagLeffler := by
  apply isMittagLeffler_sequentialHomologyTower_of_isArtinian
  intro n
  have : IsArtinian R ((K.obj (op n)).X i) := h n
  exact (K.obj (op n)).isArtinian_homology_of_isArtinian_degree i

/-- For an inverse tower K of R-module complexes of any shape over an
arbitrary ring R, if every term Kₙᵃ is Artinian, then the complex product
difference Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic. -/
theorem epi_sequentialDifference_of_degreewise_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (i : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X i)) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    ModuleCat.epi_sequentialDifference_of_isMittagLeffler (sequentialDegreeTower K i)
      (isMittagLeffler_sequentialDegreeTower_of_isArtinian K i (h i))

variable [CountableAB4Star (ModuleCat.{w} R)]

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes. Assume exact countable products in the module
category, Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).

If H_i(Kₙ) is Artinian for every stage n, then the canonical Milnor edge H_j(lim K) → lim(H_jK) is an isomorphism. -/
theorem isIso_sequentialMilnorEdge_of_isArtinian_homology
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    IsIso (sequentialMilnorEdge K hK i j hij) :=
  isIso_sequentialMilnorEdge_of_isZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian K i h))

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes. Assume exact countable products in the module
category, Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).

If Kₙᵢ is Artinian for every stage n, then the canonical Milnor edge H_j(lim K) → lim(H_jK) is an isomorphism. -/
theorem isIso_sequentialMilnorEdge_of_isArtinian_degree
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    IsIso (sequentialMilnorEdge K hK i j hij) :=
  isIso_sequentialMilnorEdge_of_isZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree K i h))

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes with every term Kₙᵃ Artinian as an R-module.
Assume exact countable products in the module category and c.Rel(i,j).

The degreewise Artinian condition makes Δ_K epic, and the resulting canonical Milnor edge H_j(lim K) → lim(H_jK) is an isomorphism. -/
theorem isIso_sequentialMilnorEdge_of_degreewise_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    IsIso (sequentialMilnorEdge K
      (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij) :=
  isIso_sequentialMilnorEdge_of_isArtinian_degree K
    (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij (h i)

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes. Assume exact countable products in the module
category, Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).

If each H_i(Kₙ) is Artinian, the canonical comparison H_j(lim K) ≅ lim(H_jK) is the isomorphism of the Milnor edge. -/
def sequentialMilnorIsoOfIsArtinianHomology
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) :=
  sequentialMilnorIsoOfIsZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian K i h))

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes with every term Kₙᵃ Artinian as an R-module.
Assume exact countable products in the module category and c.Rel(i,j).

The canonical comparison H_j(lim K) ≅ lim(H_jK), using the epic difference supplied by the Artinian terms and the Milnor edge. -/
def sequentialMilnorIsoOfDegreewiseIsArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) :=
  sequentialMilnorIsoOfIsZero K
    (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree K i (h i)))

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes. Assume exact countable products in the module
category, Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).

If each H_i(Kₙ) is Artinian, the forward map of the canonical Artinian-homology comparison equals the named Milnor edge. -/
@[simp]
theorem sequentialMilnorIsoOfIsArtinianHomology_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (sequentialMilnorIsoOfIsArtinianHomology K hK i j hij h).hom =
      sequentialMilnorEdge K hK i j hij := rfl

/-- Let R be an arbitrary ring, c a complex shape and K an inverse tower
of R-module complexes with every term Kₙᵃ Artinian as an R-module.
Assume exact countable products in the module category and c.Rel(i,j).

The forward map of the degreewise Artinian comparison equals the Milnor edge formed with the epic difference supplied by the Artinian terms. -/
@[simp]
theorem sequentialMilnorIsoOfDegreewiseIsArtinian_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorIsoOfDegreewiseIsArtinian K h i j hij).hom =
      sequentialMilnorEdge K
        (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij := rfl

end Modules

end HomologicalComplex
