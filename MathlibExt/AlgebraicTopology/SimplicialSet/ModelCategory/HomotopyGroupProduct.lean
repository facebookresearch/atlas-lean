/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

/-! # Pointed homotopy-group binary-product comparison

Pure-simplicial comparison `π n (X ⨯ A) x ≃ π n X _ × π n A _` and its
naturality for `Limits.prod.map f g`. Built from maps into categorical
products (`Limits.prod.lift`), componentwise boundary-constant conditions
(`Subcomplex.ofSimplex_ι`, `SSet.const_comp`, `SSet.comp_const`),
componentwise relative homotopies, and `π.rec` / `mk_surjective`. Handles
`n = 0` without group assumptions and assumes no `KanComplex` hypotheses.

Dependent target basepoints are aligned with `Limits.prod.map_fst` /
`map_snd` and `π.map_congr` proof irrelevance, keeping the target
basepoint implicit where possible.

Exposes only the comparison, its bijectivity, and its naturality needed to
delete `ax_bijective_piProdComparison` from `KanComplexWProduct`. Uses no
realization, `W.prodMap`, or `ModelCategory SSet`.

Explicit nonclaims: no `ModelCategory SSet` instance is used or constructed;
no public axiom is added; no group structure is assumed (works at `n = 0`).
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

/-- Pointed simplex in a binary product from component pointed simplices, via
`Limits.prod.lift`. The boundary condition follows componentwise: after
projecting, both sides reduce to `SSet.const` via `Subcomplex.ofSimplex_ι`,
`SSet.const_comp`, and `SSet.comp_const`. No Kan hypothesis. -/
private noncomputable def ptLift {X A : SSet.{u}} {n : ℕ} {x : (X ⨯ A) _⦋0⦌}
    (pX : X.PtSimplex n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x))
    (pA : A.PtSimplex n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)) :
    (X ⨯ A).PtSimplex n x where
  map := Limits.prod.lift (RelativeMorphism.map pX) (RelativeMorphism.map pA)
  comm := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.lift_fst, pX.comm,
        Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.const_comp]
    · simp only [Category.assoc, Limits.prod.lift_snd, pA.comm,
        Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.const_comp]

/-- Underlying map of a lifted pointed simplex (definitionally `prod.lift`). -/
private theorem ptLift_map {X A : SSet.{u}} {n : ℕ} {x : (X ⨯ A) _⦋0⦌}
    (pX : X.PtSimplex n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x))
    (pA : A.PtSimplex n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)) :
    RelativeMorphism.map (ptLift pX pA) =
      Limits.prod.lift (RelativeMorphism.map pX) (RelativeMorphism.map pA) :=
  rfl

/-- Componentwise relative homotopies assemble to a relative homotopy in the
binary product, via `Limits.prod.lift` of the homotopy maps. Endpoints and
the relative boundary condition follow componentwise (both sides reduce to
`SSet.const` after projecting). No Kan hypothesis. -/
private noncomputable def homotopyLift {X A : SSet.{u}} {n : ℕ}
    {x : (X ⨯ A) _⦋0⦌}
    {pX qX : X.PtSimplex n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x)}
    {pA qA : A.PtSimplex n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)}
    (hX : PtSimplex.Homotopy pX qX) (hA : PtSimplex.Homotopy pA qA) :
    PtSimplex.Homotopy (ptLift pX pA) (ptLift qX qA) where
  h := Limits.prod.lift hX.h hA.h
  h₀ := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.lift_fst, hX.h₀, ptLift_map]
    · simp only [Category.assoc, Limits.prod.lift_snd, hA.h₀, ptLift_map]
  h₁ := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.lift_fst, hX.h₁, ptLift_map]
    · simp only [Category.assoc, Limits.prod.lift_snd, hA.h₁, ptLift_map]
  rel := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.lift_fst, hX.rel,
        Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.const_comp]
    · simp only [Category.assoc, Limits.prod.lift_snd, hA.rel,
        Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.const_comp]

/-- First projection of a lifted pointed simplex recovers the input
(`Limits.prod.lift_fst` under `RelativeMorphism.ext`). -/
private theorem ptLift_fst {X A : SSet.{u}} {n : ℕ} {x : (X ⨯ A) _⦋0⦌}
    (pX : X.PtSimplex n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x))
    (pA : A.PtSimplex n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)) :
    PtSimplex.map (Limits.prod.fst : X ⨯ A ⟶ X) rfl (ptLift pX pA) = pX := by
  apply RelativeMorphism.ext
  exact Limits.prod.lift_fst _ _

/-- Second projection of a lifted pointed simplex recovers the input
(`Limits.prod.lift_snd` under `RelativeMorphism.ext`). -/
private theorem ptLift_snd {X A : SSet.{u}} {n : ℕ} {x : (X ⨯ A) _⦋0⦌}
    (pX : X.PtSimplex n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x))
    (pA : A.PtSimplex n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)) :
    PtSimplex.map (Limits.prod.snd : X ⨯ A ⟶ A) rfl (ptLift pX pA) = pA := by
  apply RelativeMorphism.ext
  exact Limits.prod.lift_snd _ _

/-- Lifting the two projections recovers the original pointed simplex
(product eta via `Limits.prod.hom_ext`). -/
private theorem ptLift_eta {X A : SSet.{u}} {n : ℕ} {x : (X ⨯ A) _⦋0⦌}
    (p : (X ⨯ A).PtSimplex n x) :
    ptLift (PtSimplex.map (Limits.prod.fst : X ⨯ A ⟶ X) rfl p)
      (PtSimplex.map (Limits.prod.snd : X ⨯ A ⟶ A) rfl p) = p := by
  apply RelativeMorphism.ext
  apply Limits.prod.hom_ext
  · exact Limits.prod.lift_fst _ _
  · exact Limits.prod.lift_snd _ _

/-- Inverse of the comparison on representatives, descended to homotopy
classes via `Quot.lift₂`. Well-definedness in each argument is a single
componentwise homotopy step (the other side uses `Homotopy.refl`); no Kan
hypothesis and no group structure (works at `n = 0`). -/
private noncomputable def piProdInv {X A : SSet.{u}} (n : ℕ)
    (x : (X ⨯ A) _⦋0⦌)
    (p : π n X ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x) ×
      π n A ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x)) :
    π n (X ⨯ A) x :=
  Quot.lift₂ (fun pX pA => π.mk (ptLift pX pA)) (by
    intro pX pA qA h
    obtain ⟨hA⟩ := h
    exact (homotopyLift (RelativeMorphism.Homotopy.refl pX) hA).eq) (by
    intro pX qX pA h
    obtain ⟨hX⟩ := h
    exact (homotopyLift hX (RelativeMorphism.Homotopy.refl pA)).eq) p.1 p.2

/-- Canonical comparison map from a pointed homotopy group of a binary product
to the product of pointed homotopy groups, induced by the two projections.
Formal definition (no seam). -/
noncomputable def piProdComparison {X A : SSet.{u}} (n : ℕ)
    (x : (X ⨯ A) _⦋0⦌) :
    π n (X ⨯ A) x →
      π n X ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x) ×
        π n A ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x) :=
  fun q => (π.map (Limits.prod.fst : X ⨯ A ⟶ X) rfl n q,
    π.map (Limits.prod.snd : X ⨯ A ⟶ A) rfl n q)

/-- Pointed product comparison equivalence, from the explicit inverse built by
`ptLift` / `homotopyLift` and descended via `Quot.lift₂`. The two-sided
inverse laws use `π.rec` (left) and `mk_surjective` (right) plus the
pointed-simplex eta/projection identities; no Kan hypothesis, works at
`n = 0`. -/
private noncomputable def piProdEquiv {X A : SSet.{u}} (n : ℕ) (x : (X ⨯ A) _⦋0⦌) :
    π n (X ⨯ A) x ≃
      π n X ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x) ×
        π n A ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x) where
  toFun := piProdComparison n x
  invFun := piProdInv n x
  left_inv := by
    intro q
    induction q using π.rec with
    | mk p =>
      show piProdInv n x (piProdComparison n x (π.mk p)) = π.mk p
      rw [show piProdComparison n x (π.mk p) =
        (π.mk (PtSimplex.map (Limits.prod.fst : X ⨯ A ⟶ X) rfl p),
          π.mk (PtSimplex.map (Limits.prod.snd : X ⨯ A ⟶ A) rfl p)) from rfl]
      change π.mk (ptLift _ _) = π.mk p
      rw [ptLift_eta]
  right_inv := by
    intro p
    obtain ⟨qx, qa⟩ := p
    obtain ⟨pX, rfl⟩ := π.mk_surjective qx
    obtain ⟨pA, rfl⟩ := π.mk_surjective qa
    show piProdComparison n x (piProdInv n x (π.mk pX, π.mk pA)) =
      (π.mk pX, π.mk pA)
    change piProdComparison n x (π.mk (ptLift pX pA)) = _
    simp only [piProdComparison, π.map_mk, ptLift_fst, ptLift_snd]

/-- Bijectivity of the static product comparison map. This is the exact
statement needed to delete `ax_bijective_piProdComparison` from
`KanComplexWProduct` (via its `Equiv.bijective`). No Kan hypothesis. -/
theorem bijective_piProdComparison {X A : SSet.{u}} (n : ℕ)
    (x : (X ⨯ A) _⦋0⦌) :
    Function.Bijective (piProdComparison (X := X) (A := A) n x) :=
  (piProdEquiv n x).bijective

/-- Intertwining equality: the `π` comparison through `prod.map f g` equals
the product of the factor `π` maps (with basepoints transported along the
vertex projection facts) through the comparison. Proved formally from
`π.map_comp_apply` and the `prod.map_fst` / `prod.map_snd` characterizations. -/
theorem piProdComparison_prodMap {X Y A B : SSet.{u}} {f : X ⟶ Y}
    {g : A ⟶ B} (n : ℕ) (x : (X ⨯ A) _⦋0⦌)
    (q : π n (X ⨯ A) x) :
    piProdComparison n ((Limits.prod.map f g).app _ x)
        (π.map (Limits.prod.map f g) rfl n q) =
      Prod.map
        (π.map f
          ((congrArg (·.app _ x) (Limits.prod.map_fst f g)).symm) n)
        (π.map g
          ((congrArg (·.app _ x) (Limits.prod.map_snd f g)).symm) n)
        (piProdComparison n x q) := by
  simp only [piProdComparison]
  apply Prod.ext
  · have hFstEq :=
      (congrArg (·.app _ x) (Limits.prod.map_fst f g)).symm
    have lhs1 : π.map (Limits.prod.fst : Y ⨯ B ⟶ Y) rfl n
          (π.map (Limits.prod.map f g) rfl n q) =
        π.map (Limits.prod.map f g ≫ Limits.prod.fst) rfl n q :=
      (π.map_comp_apply _ _ rfl rfl rfl q).symm
    have rhs1 : π.map f hFstEq n
          (π.map (Limits.prod.fst : X ⨯ A ⟶ X) rfl n q) =
        π.map (Limits.prod.fst ≫ f) hFstEq n q :=
      (π.map_comp_apply _ _ rfl hFstEq hFstEq q).symm
    have mapEq : π.map (Limits.prod.map f g ≫ Limits.prod.fst) rfl n q =
        π.map (Limits.prod.fst ≫ f) hFstEq n q :=
      congrArg (· q) (π.map_congr (Limits.prod.map_fst f g) rfl hFstEq n)
    exact lhs1.trans (mapEq.trans rhs1.symm)
  · have hSndEq :=
      (congrArg (·.app _ x) (Limits.prod.map_snd f g)).symm
    have lhs2 : π.map (Limits.prod.snd : Y ⨯ B ⟶ B) rfl n
          (π.map (Limits.prod.map f g) rfl n q) =
        π.map (Limits.prod.map f g ≫ Limits.prod.snd) rfl n q :=
      (π.map_comp_apply _ _ rfl rfl rfl q).symm
    have rhs2 : π.map g hSndEq n
          (π.map (Limits.prod.snd : X ⨯ A ⟶ A) rfl n q) =
        π.map (Limits.prod.snd ≫ g) hSndEq n q :=
      (π.map_comp_apply _ _ rfl hSndEq hSndEq q).symm
    have mapEq : π.map (Limits.prod.map f g ≫ Limits.prod.snd) rfl n q =
        π.map (Limits.prod.snd ≫ g) hSndEq n q :=
      congrArg (· q) (π.map_congr (Limits.prod.map_snd f g) rfl hSndEq n)
    exact lhs2.trans (mapEq.trans rhs2.symm)

end KanComplex

end SSet
