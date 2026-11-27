/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemialgebraicProjection
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# General real semialgebraic family trivializations

The domain and graphs use the actual finite Boolean polynomial definition
ported from Tau. Maps may be arbitrary continuous semialgebraic maps;
they need not be polynomial. The fibres below are actual inverse images,
and each trivialization is a homeomorphism with semialgebraic graphs in
both directions, commuting with the given map.

Closure under projection over the reals (Tarski--Seidenberg) is proved in the
TauCeti source by cylindrical algebraic decomposition but is not ported: the
lemmas below that need it take `[HasSemialgebraicProjections ℝ]`, and the
real instance is a separate wanted statement. Neither a CAD nor a family
homeomorphism is assumed by the set or map definitions.

Sources: R. M. Hardt, *Semi-Algebraic Local-Triviality in Semi-Algebraic
Mappings*, Amer. J. Math. 102 (1980), 291--302,
https://doi.org/10.2307/2374240, main triviality theorem;
Hardt--Lambrechts--Turchin--Volic, *Real homotopy theory of semi-algebraic
sets*, Algebr. Geom. Topol. 11 (2011), 2477--2545, Section 2, p. 2483,
https://doi.org/10.2140/agt.2011.11.2477.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemialgebraicTriviality

open Set TauCeti

abbrev RealSpace (n : ℕ) := Fin n → ℝ

/-- Extend only the underlying values outside the specified domain.
Semialgebraicity is tested on the actual domain, so this default adds no
condition on the map there. -/
def ambientMap {α β : Type} {s : Set (α → ℝ)} {t : Set (β → ℝ)}
    (f : s → t) : (α → ℝ) → (β → ℝ) := by
  classical
  exact fun x ↦ if h : x ∈ s then (f ⟨x, h⟩).val else 0

@[simp]
theorem ambientMap_subtype {α β : Type} {s : Set (α → ℝ)} {t : Set (β → ℝ)}
    (f : s → t) (x : s) : ambientMap f x.val = (f x).val := by
  simp [ambientMap, x.property]

/-- A genuine Euclidean homeomorphism with actual semialgebraic graphs. -/
structure SemialgebraicHomeomorphism {α β : Type}
    (s : Set (α → ℝ)) (t : Set (β → ℝ)) where
  homeomorph : s ≃ₜ t
  semialgebraic : IsSemialgebraicOn (ambientMap homeomorph) s
  semialgebraic_inverse : IsSemialgebraicOn (ambientMap homeomorph.symm) t

/-- The actual fibre of the specified map on its specified domain. -/
def fiber {m n : ℕ} (s : Set (RealSpace m)) (f : RealSpace m → RealSpace n)
    (b : RealSpace n) : Set (RealSpace m) := s ∩ f ⁻¹' {b}

/-- The actual inverse image of a base piece within the map's domain. -/
def patch {m n : ℕ} (s : Set (RealSpace m)) (f : RealSpace m → RealSpace n)
    (b : Set (RealSpace n)) : Set (RealSpace m) := s ∩ f ⁻¹' b

/-- A product is encoded in the real coordinate space of the disjoint sum. -/
def coordinateProduct {α β : Type} (s : Set (α → ℝ)) (t : Set (β → ℝ)) :
    Set (α ⊕ β → ℝ) := Equiv.sumArrowEquivProdArrow α β ℝ ⁻¹' s ×ˢ t

/-- The actual point of that product, retaining both factors' coordinates. -/
def productPoint {α β : Type} {s : Set (α → ℝ)} {t : Set (β → ℝ)}
    (x : s) (y : t) : coordinateProduct s t :=
  ⟨Sum.elim x.val y.val, x.property, y.property⟩

/-- A polynomial coordinate map is continuous in the Euclidean topology. -/
theorem polynomialMap_continuous {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) :
    Continuous (fun x : RealSpace m ↦ fun i ↦ MvPolynomial.eval x (p i)) :=
  continuous_pi fun i ↦ MvPolynomial.continuous_eval (p i)

/-- The completed projection API proves semialgebraicity of actual fibres. -/
theorem fiber_semialgebraic [HasSemialgebraicProjections ℝ] {m n : ℕ}
    {s : Set (RealSpace m)} {f : RealSpace m → RealSpace n}
    (hf : IsSemialgebraicOn f s) (b : RealSpace n) :
    IsSemialgebraic (fiber s f b) :=
  hf.isSemialgebraic_inter_preimage (isSemialgebraic_singleton b)

/-- The same source-proved API applies to arbitrary semialgebraic base pieces. -/
theorem patch_semialgebraic [HasSemialgebraicProjections ℝ] {m n : ℕ}
    {s : Set (RealSpace m)} {f : RealSpace m → RealSpace n}
    (hf : IsSemialgebraicOn f s) {b : Set (RealSpace n)} (hb : IsSemialgebraic b) :
    IsSemialgebraic (patch s f b) := hf.isSemialgebraic_inter_preimage hb

/-- Products of actual semialgebraic sets are actual semialgebraic sets. -/
theorem coordinateProduct_semialgebraic {α β : Type}
    {s : Set (α → ℝ)} {t : Set (β → ℝ)}
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (coordinateProduct s t) :=
  hs.preimage_sumArrowEquivProdArrow_prod ht

/-- Hardt data over a finite base partition, using the actual reference
fibre rather than a supplied abstract fibre carrier. -/
structure HardtTrivialization {m n : ℕ} (s : Set (RealSpace m))
    (f : RealSpace m → RealSpace n) where
  count : ℕ
  base : Fin count → Set (RealSpace n)
  base_semialgebraic : ∀ i, IsSemialgebraic (base i)
  cover : (⋃ i, base i) = f '' s
  disjoint : Pairwise fun i j ↦ Disjoint (base i) (base j)
  reference : ∀ i, base i
  trivialization : ∀ i, SemialgebraicHomeomorphism
    (coordinateProduct (base i) (fiber s f (reference i).val)) (patch s f (base i))
  projection : ∀ i (z : coordinateProduct (base i) (fiber s f (reference i).val)),
    f ((trivialization i).homeomorph z).val = z.val ∘ Sum.inl
  reference_identity : ∀ i (x : fiber s f (reference i).val),
    ((trivialization i).homeomorph (productPoint (reference i) x)).val = x.val

/-- Every chosen reference point really lies in the original map's image. -/
theorem HardtTrivialization.reference_mem_image {m n : ℕ}
    {s : Set (RealSpace m)} {f : RealSpace m → RealSpace n}
    (t : HardtTrivialization s f) (i : Fin t.count) : (t.reference i).val ∈ f '' s := by
  rw [← t.cover]
  exact mem_iUnion.mpr ⟨i, (t.reference i).property⟩

/-- The fixed fibre in each nonempty base piece is itself nonempty. -/
theorem HardtTrivialization.fiber_nonempty {m n : ℕ}
    {s : Set (RealSpace m)} {f : RealSpace m → RealSpace n}
    (t : HardtTrivialization s f) (i : Fin t.count) :
    (fiber s f (t.reference i).val).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := t.reference_mem_image i
  exact ⟨x, hx, hfx⟩

end MathlibExt.AlgebraicGeometry.SemialgebraicTriviality
