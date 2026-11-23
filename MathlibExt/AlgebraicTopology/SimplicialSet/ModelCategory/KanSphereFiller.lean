/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SphereFaceCorrection
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction

/-! # Sphere fillers in weakly contractible Kan complexes

Given a Kan complex `F` with a chosen vertex `x₀` whose pointed homotopy
groups `π n F x` are subsingletons for every `n` and every basepoint `x`,
every boundary sphere `s : ∂Δ[n] ⟶ F` extends over `Δ[n]`.

Live proof by ordinary induction on `n`. The `n = 0` case is the constant map
at `x₀` by boundary extensionality. For the step `A(m) → A(m + 1)`, fill the
strictly lower-dimensional ridge of the chosen face by the induction
hypothesis, contract that filler with `homotopyIdConstLast`, use two strict
`{0}`-cap anodyne homotopy extensions (first in `Δ[m]` to a constant-ridge
face, second from the face subcomplex into the boundary to a modified boundary
map), fill the resulting horn by Kan filling, use pointed `π`
subsingletonness plus the accepted face-correction theorem
`exists_correct_face_of_HomotopyRel` to swap in the true face, then transport
back through a strict `{1}`-capped prism (anodyne by pushout-product),
restricting at `ι₀` to a filler of the original sphere. Only strictly
lower-dimensional fillers, Kan horn fillers, single-cap anodyne lifts, and the
provider are used.

Explicit nonclaims: no `I.rlp` characterization, no minimal-fibration theorem,
no model-category instance, and no generated-root change.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial SSet
  Opposite
open scoped Simplicial

namespace SSet.KanComplex

variable {F : SSet.{u}} [KanComplex F]

omit [KanComplex F] in
private theorem filler_zero (x₀ : F _⦋0⦌) (s : (∂Δ[0] : SSet.{u}) ⟶ F) :
    ∃ _t : Δ[0] ⟶ F, (SSet.boundary 0).ι ≫ _t = s :=
  ⟨SSet.const x₀, SSet.boundary.hom_ext₀⟩

/-- Capped-cylinder subcomplex for the prism cap step:
`(∂Δ[n] × Δ[1]) ∪ (Δ[n] × {1})`. -/
private noncomputable def capSubcomplex (n : ℕ) :
    (Δ[n] ⊗ (Δ[1] : SSet.{u})).Subcomplex :=
  (SSet.boundary n).unionProd
    (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)

/-- The capped-cylinder inclusion is anodyne, by pushout-product with the
`{1}`-vertex horn inclusion. -/
private theorem cap_mem_anodyneExtensions (n : ℕ) :
    SSet.anodyneExtensions.{u} (capSubcomplex (n := n)).ι := by
  have h_face : SSet.anodyneExtensions.{u}
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
    have h_eq : (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) =
        SSet.horn (n := 1) (1 : Fin 2) := by
      have h_fin : ({1} : Finset (Fin 2)) = {0}ᶜ := by decide
      calc (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)
          = SSet.stdSimplex.face ({0}ᶜ : Finset (Fin 2)) := by rw [h_fin]
        _ = SSet.horn (n := 1) (1 : Fin 2) := by
            ext m x
            simp [SSet.horn_eq_iSup]
    rw [h_eq]
    exact SSet.anodyneExtensions.horn_ι (1 : Fin 2)
  have h : SSet.anodyneExtensions.{u}
      ((SSet.boundary n).unionProd
        (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι :=
    SSet.anodyneExtensions_unionProd_ι (SSet.boundary n) _ h_face
  simpa [capSubcomplex] using h

/-- Every horn sits inside the boundary. -/
private theorem horn_le_boundary {n : ℕ} (i : Fin (n + 1)) :
    SSet.horn n i ≤ SSet.boundary n := by
  rw [SSet.horn_eq_iSup]
  refine iSup_le fun j ↦ ?_
  exact SSet.face_singleton_compl_le_boundary j.1

/-- Kan filler of the restriction of a boundary sphere to a horn. -/
private noncomputable def hornFill {n : ℕ} (i : Fin (n + 2))
    (s : (∂Δ[n + 1] : SSet.{u}) ⟶ F) : Δ[n + 1] ⟶ F :=
  (SSet.KanComplex.hornFilling
    (Subcomplex.homOfLE (horn_le_boundary i) ≫ s)).choose

/-- The horn filler extends the restricted sphere. -/
private theorem hornFill_spec {n : ℕ} (i : Fin (n + 2))
    (s : (∂Δ[n + 1] : SSet.{u}) ⟶ F) :
    Subcomplex.homOfLE (horn_le_boundary i) ≫ s =
      (SSet.horn (n + 1) i).ι ≫ hornFill i s :=
  (SSet.KanComplex.hornFilling _).choose_spec

/-! ## All-dimensional induction step

Given `s : ∂Δ[m + 1] ⟶ F`, pick the `k`-th face. Its ridge is the
`(m - 1)`-sphere `b = ∂Δ[m] → F` obtained by restricting `s`. The induction
hypothesis fills `b` to `c : Δ[m] ⟶ F`; whiskering the contraction
`homotopyIdConstLast m` with `c` gives a null-homotopy of `b`. A first
single-cap homotopy extension in `Δ[m]` turns the chosen face into one with
constant ridge; a second single-cap extension from the face (as the range
subcomplex of `∂Δ[m + 1]`) into the boundary moves `s` to `s'` with constant
ridge. The horn of `s'` is filled, the two constant-ridge faces are related
by pointed `π` subsingletonness, the accepted face-correction provider swaps
in the true face, and the filler is transported back along the boundary
homotopy through the capped prism. Only strictly lower-dimensional fillers,
Kan horn fillers, single-cap anodyne lifts, and the provider are used.
-/

/-- The `k`-th face inclusion into the boundary, as a map `Δ[m] ⟶ ∂Δ[m + 1]`. -/
private noncomputable def faceInclBd (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ⟶ (∂Δ[m + 1] : SSet.{u}) :=
  (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
    Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary k)

/-- The face inclusion projects to `δ k`. -/
private theorem faceInclBd_ι (m : ℕ) (k : Fin (m + 2)) :
    faceInclBd m k ≫ (SSet.boundary (m + 1)).ι = SSet.stdSimplex.δ k := by
  rw [faceInclBd, Category.assoc, Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι]

/-- The ridge sits in the complementary horn: the range of
`(boundary m).ι ≫ δ k` lies in `Λ[m + 1, k]`. If `z` misses `j'`, then
`δ k z` misses `k.succAbove j' ≠ k`. -/
private theorem ridge_le_horn (m : ℕ) (k : Fin (m + 2)) :
    Subcomplex.range ((SSet.boundary m).ι ≫ SSet.stdSimplex.δ k) ≤
      SSet.horn (m + 1) k := by
  intro n x hx
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨zval, hz⟩ := z
  obtain ⟨j', hj'⟩ := (SSet.mem_boundary_iff_notMem_range _).mp hz
  refine (SSet.mem_horn_iff_notMem_range _ _).mpr
    ⟨k.succAbove j', Fin.succAbove_ne _ _, ?_⟩
  rintro ⟨a, ha⟩
  apply hj'
  refine ⟨a, ?_⟩
  have hδ : (SSet.stdSimplex.δ k).app _ zval a = k.succAbove (zval a) := rfl
  have hxa : (SSet.stdSimplex.δ k).app _ zval a = k.succAbove j' := ha
  rw [hδ] at hxa
  exact Fin.succAbove_right_injective hxa

/-- The ridge inclusion into the complementary horn. -/
private noncomputable def ridgeToHorn (m : ℕ) (k : Fin (m + 2)) :
    (∂Δ[m] : SSet.{u}) ⟶ (SSet.horn (m + 1) k : SSet.{u}) :=
  Subcomplex.lift _ (ridge_le_horn m k)

/-- The ridge-to-horn lift projects to the ridge followed by `δ k`. -/
private theorem ridgeToHorn_spec (m : ℕ) (k : Fin (m + 2)) :
    ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι =
      (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k :=
  Subcomplex.lift_ι _ _

/-- Null-homotopy of the ridge `b = boundary.ι ≫ c`, by whiskering the
simplex contraction with the filler `c`. -/
private noncomputable def ridgeNullMap (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    (∂Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫
    (SSet.stdSimplex.homotopyIdConstLast m).h ≫ c

omit [KanComplex F] in
/-- The null-homotopy starts at the ridge. -/
private theorem ridgeNullMap_h₀ (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    SSet.ι₀ ≫ ridgeNullMap m c = (SSet.boundary m).ι ≫ c := by
  have e : SSet.ι₀ ≫ ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) =
      (SSet.boundary m).ι ≫ SSet.ι₀ :=
    SSet.ι₀_comp _
  have h0 : SSet.ι₀ ≫
      ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c) =
      𝟙 _ ≫ c := by
    rw [← Category.assoc, (SSet.stdSimplex.homotopyIdConstLast m).h₀]
  calc SSet.ι₀ ≫ ridgeNullMap m c
      = (SSet.boundary m).ι ≫ (SSet.ι₀ ≫
          ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c)) := by
        rw [ridgeNullMap, ← Category.assoc, ← Category.assoc, e, Category.assoc,
          Category.assoc]
    _ = (SSet.boundary m).ι ≫ c := by rw [h0, Category.id_comp]

omit [KanComplex F] in
/-- The null-homotopy ends at the constant map on the last-vertex value. -/
private theorem ridgeNullMap_h₁ (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    SSet.ι₁ ≫ ridgeNullMap m c =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have e : SSet.ι₁ ≫ ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) =
      (SSet.boundary m).ι ≫ SSet.ι₁ :=
    SSet.ι₁_comp _
  have h1 : SSet.ι₁ ≫
      ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c) =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
    rw [← Category.assoc, (SSet.stdSimplex.homotopyIdConstLast m).h₁]
    exact SSet.const_comp _ _
  calc SSet.ι₁ ≫ ridgeNullMap m c
      = (SSet.boundary m).ι ≫ (SSet.ι₁ ≫
          ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c)) := by
        rw [ridgeNullMap, ← Category.assoc, ← Category.assoc, e, Category.assoc,
          Category.assoc]
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
        rw [h1]
        exact SSet.comp_const _ _

/-- The `{0}`-vertex inclusion into `Δ[1]` is anodyne (it is `Λ[1, 0]`). -/
private theorem faceZero_mem_anodyne :
    SSet.anodyneExtensions.{u}
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
      SSet.horn (n := 1) (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
        = SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = SSet.horn (n := 1) (0 : Fin 2) := by
          ext m x
          simp [SSet.horn_eq_iSup]
  rw [h_eq]
  exact SSet.anodyneExtensions.horn_ι (0 : Fin 2)

omit [KanComplex F] in
/-- Agreement for the first homotopy extension: the constant face map and the
ridge null-homotopy agree on `∂Δ[m] ⊗ {0}`, since `{0}`-simplices are constant
`0` and the null-homotopy starts at the ridge. -/
private theorem agree1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    ((SSet.boundary m).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ fk) =
      (((SSet.boundary m : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ridgeNullMap m c) := by
  ext n ⟨⟨z, hz⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have ht0 : ∀ a, t a = (0 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  have hpair : (⟨⟨z, hz⟩, ((SSet.stdSimplex.face {0} :
      (Δ[1] : SSet.{u}).Subcomplex).ι.app _ ⟨t, ht⟩)⟩ :
      ((((SSet.boundary m : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
        (Opposite.op ⦋d⦌)))) =
      SSet.ι₀.app _ (⟨z, hz⟩ : ((SSet.boundary m : SSet.{u}).obj
        (Opposite.op ⦋d⦌))) := by
    refine Prod.ext rfl ?_
    dsimp only
    change t = _
    ext a
    simp only [ht0]
    congr 1
  have hH0 : (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
        ⟨t, ht⟩)⟩ =
      ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := by
    calc (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
          ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩
        = (ridgeNullMap m c).app _ (SSet.ι₀.app _ ⟨z, hz⟩) := by rw [← hpair]
      _ = (SSet.ι₀ ≫ ridgeNullMap m c).app _ ⟨z, hz⟩ := rfl
      _ = ((SSet.boundary m).ι ≫ c).app _ ⟨z, hz⟩ := by rw [ridgeNullMap_h₀]
      _ = ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := by rw [hbc]
  have hgoal : ((((SSet.boundary m).ι ▷
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ fk)).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩) =
      ((((SSet.boundary m : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ridgeNullMap m c).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩) := by
    calc ((((SSet.boundary m).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
        (fst _ _ ≫ fk)).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩)
        = fk.app _ z := rfl
      _ = ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := rfl
      _ = (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
          ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩ := hH0.symm
      _ = _ := rfl
  exact hgoal

omit [KanComplex F] in
/-- Endpoint law: `ι₀` lands in the `{0}`-cap, so a lift extending the
`{0}`-side restricts at `ι₀` to the base map. Proved pointwise to avoid
fragile associativity rewriting. -/
private theorem iota_zero_of_lift {X : SSet.{u}} (S : X.Subcomplex) (f : X ⟶ F)
    (Φ : X ⊗ (Δ[1] : SSet.{u}) ⟶ F)
    (gR : ((S.unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶ F)
    (hgR1 : Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0}) ≫ gR =
      fst _ _ ≫ f)
    (hΦlift : (S.unionProd (SSet.stdSimplex.face {0})).ι ≫ Φ = gR) :
    SSet.ι₀ ≫ Φ = f := by
  ext n x
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have hmem2 : (SSet.ι₀.app (Opposite.op ⦋d⦌) x).2 ∈
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).obj
        (Opposite.op ⦋d⦌) := by
    rw [SSet.stdSimplex.mem_face_iff]
    intro i
    exact Finset.mem_singleton.mpr (SSet.ι₀_app_snd_apply x i)
  have hmem : SSet.ι₀.app (Opposite.op ⦋d⦌) x ∈
      (S.unionProd (SSet.stdSimplex.face {0})).obj (Opposite.op ⦋d⦌) :=
    Or.inl ⟨Set.mem_univ _, hmem2⟩
  have e1 : Φ.app _ (SSet.ι₀.app _ x) =
      gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ := by
    have h := congrArg (fun ψ :
        ((S.unionProd (SSet.stdSimplex.face {0})) : SSet.{u}) ⟶ F =>
        ψ.app _ ⟨SSet.ι₀.app _ x, hmem⟩) hΦlift
    exact h
  have e2 : (⟨SSet.ι₀.app _ x, hmem⟩ :
      ((S.unionProd (SSet.stdSimplex.face {0})) : SSet.{u}).obj _) =
      (Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0})).app _ ⟨x,
        ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := by
    apply Subtype.ext
    change SSet.ι₀.app _ x = _
    rfl
  have e3 : gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ = f.app _ x := by
    calc gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩
        = gR.app _ ((Subcomplex.unionProd.ι₁ S
            (SSet.stdSimplex.face {0})).app _ ⟨x,
              ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩) := by rw [← e2]
      _ = (Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0}) ≫ gR).app _
          ⟨x, ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := rfl
      _ = (fst X ((SSet.stdSimplex.face {0} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫ f).app _
          ⟨x, ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := by rw [hgR1]
      _ = f.app _ x := rfl
  calc (SSet.ι₀ ≫ Φ).app _ x = Φ.app _ (SSet.ι₀.app _ x) := rfl
    _ = gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ := e1
    _ = f.app _ x := e3

omit [KanComplex F] in
/-- Glued map on the `{0}`-cap prism over `Δ[m]`: the constant face map on
the base side, the ridge null-homotopy on the boundary side. -/
private noncomputable def gR1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶ F :=
  (Subcomplex.unionProd.isPushout (SSet.boundary m)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ fk) (ridgeNullMap m c) (agree1 m fk c hbc)

omit [KanComplex F] in
/-- The `{0}`-cap prism over `Δ[m]` is anodyne, by the pushout-product theorem. -/
private theorem cap1_mem_anodyne (m : ℕ) :
    SSet.anodyneExtensions (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι) :=
  SSet.anodyneExtensions_unionProd_ι _ _ faceZero_mem_anodyne

/-- First homotopy extension: the glued cap map extends over `Δ[m] ⊗ Δ[1]`. -/
private noncomputable def lift1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gR1 m fk c hbc)
    (cap1_mem_anodyne m)).choose

private theorem lift1_spec (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      lift1 m fk c hbc) = gR1 m fk c hbc :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gR1 m fk c hbc)
    (cap1_mem_anodyne m)).choose_spec

/-- The extension starts at the chosen face. -/
private theorem lift1_zero (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    SSet.ι₀ ≫ lift1 m fk c hbc = fk := by
  have hg := (Subcomplex.unionProd.isPushout (SSet.boundary m)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inl_desc
    (fst _ _ ≫ fk) (ridgeNullMap m c) (agree1 m fk c hbc)
  exact iota_zero_of_lift _ _ _ _ hg (lift1_spec m fk c hbc)

/-- The new face: restriction of the first extension to `{1}`. -/
private noncomputable def fk' (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (Δ[m] : SSet.{u}) ⟶ F :=
  SSet.ι₁ ≫ lift1 m fk c hbc

/-- The new face has constant ridge, at the last-vertex value of `c`. -/
private theorem fk'_ridge (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (SSet.boundary m).ι ≫ fk' m fk c hbc =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have hside : ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc =
      ridgeNullMap m c := by
    rw [← Subcomplex.unionProd.ι₂_ι (SSet.boundary m)
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, lift1_spec m fk c hbc]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  calc (SSet.boundary m).ι ≫ fk' m fk c hbc
      = (SSet.boundary m).ι ≫ (SSet.ι₁ ≫ lift1 m fk c hbc) := rfl
    _ = SSet.ι₁ ≫ (((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫
          lift1 m fk c hbc) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₁_comp]
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
        rw [hside, ridgeNullMap_h₁]

omit [KanComplex F] in
/-- The `k`-th face, as a subcomplex of the boundary `∂Δ[m + 1]`: the
preimage of the face `{k}ᶜ` along the boundary inclusion. -/
private noncomputable def faceSubBd (m : ℕ) (k : Fin (m + 2)) :
    (∂Δ[m + 1] : SSet.{u}).Subcomplex :=
  Subcomplex.preimage (SSet.stdSimplex.face {k}ᶜ)
    (SSet.boundary (m + 1)).ι

omit [KanComplex F] in
private theorem faceSubBd_range_le (m : ℕ) (k : Fin (m + 2)) :
    Subcomplex.range (faceInclBd m k) ≤ faceSubBd m k := by
  intro N y hy
  obtain ⟨z, rfl⟩ := hy
  change (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z) ∈
    (SSet.stdSimplex.face {k}ᶜ).obj N
  have e : (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z) =
      (SSet.stdSimplex.δ k).app N z := by
    calc (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z)
        = ((faceInclBd m k ≫ (SSet.boundary (m + 1)).ι).app N z) := rfl
      _ = ((SSet.stdSimplex.δ k).app N z) := by rw [faceInclBd_ι m k]
  rw [e, ← SSet.stdSimplex.range_δ]
  exact ⟨z, rfl⟩

omit [KanComplex F] in
/-- The face inclusion lifts to the face subcomplex of the boundary. -/
private noncomputable def faceSubBdHom (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ⟶ ((faceSubBd m k : SSet.{u})) :=
  Subcomplex.lift (faceInclBd m k) (faceSubBd_range_le m k)

omit [KanComplex F] in
/-- Projecting the face subcomplex back to `Δ[m]` through the face iso. -/
private noncomputable def faceSubBdInv (m : ℕ) (k : Fin (m + 2)) :
    ((faceSubBd m k : SSet.{u})) ⟶ (Δ[m] : SSet.{u}) :=
  Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
    (SSet.boundary (m + 1)).ι ≫
    (SSet.stdSimplex.faceSingletonComplIso k).inv

omit [KanComplex F] in
/-- The face inclusion is a retraction onto the face subcomplex of the
boundary: projecting back through the face iso recovers the identity. -/
private theorem faceSubBd_hom_inv (m : ℕ) (k : Fin (m + 2)) :
    faceSubBdHom m k ≫ faceSubBdInv m k = 𝟙 _ := by
  have hH : faceSubBdHom m k ≫ (faceSubBd m k).ι = faceInclBd m k := rfl
  have hFP : Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
        (SSet.boundary (m + 1)).ι ≫ (SSet.stdSimplex.face {k}ᶜ).ι =
      (faceSubBd m k).ι ≫ (SSet.boundary (m + 1)).ι := rfl
  have hface : faceSubBdHom m k ≫
      Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
        (SSet.boundary (m + 1)).ι =
      (SSet.stdSimplex.faceSingletonComplIso k).hom := by
    apply (cancel_mono (SSet.stdSimplex.face {k}ᶜ).ι).mp
    calc (faceSubBdHom m k ≫
              Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι) ≫
            (SSet.stdSimplex.face {k}ᶜ).ι
        = faceSubBdHom m k ≫
            (Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι ≫
              (SSet.stdSimplex.face {k}ᶜ).ι) :=
          Category.assoc _ _ _
      _ = faceSubBdHom m k ≫
            ((faceSubBd m k).ι ≫ (SSet.boundary (m + 1)).ι) :=
          congrArg (faceSubBdHom m k ≫ ·) hFP
      _ = (faceSubBdHom m k ≫ (faceSubBd m k).ι) ≫
            (SSet.boundary (m + 1)).ι :=
          (Category.assoc _ _ _).symm
      _ = faceInclBd m k ≫ (SSet.boundary (m + 1)).ι :=
          congrArg (· ≫ (SSet.boundary (m + 1)).ι) hH
      _ = SSet.stdSimplex.δ k := faceInclBd_ι m k
      _ = (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
            (SSet.stdSimplex.face {k}ᶜ).ι :=
          (SSet.stdSimplex.faceSingletonComplIso_hom_ι _).symm
  calc faceSubBdHom m k ≫ faceSubBdInv m k
      = faceSubBdHom m k ≫ (Subcomplex.fromPreimage
            (SSet.stdSimplex.face {k}ᶜ) (SSet.boundary (m + 1)).ι ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv) := rfl
    _ = (faceSubBdHom m k ≫ Subcomplex.fromPreimage
            (SSet.stdSimplex.face {k}ᶜ) (SSet.boundary (m + 1)).ι) ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv :=
        (Category.assoc _ _ _).symm
    _ = (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv :=
        congrArg (· ≫ (SSet.stdSimplex.faceSingletonComplIso k).inv) hface
    _ = 𝟙 _ := Iso.hom_inv_id _

omit [KanComplex F] in
/-- A pair with `{0}`-second component equals the `ι₀` image of its first
component. Generalizes the `hpair` step of `agree1`. -/
private theorem iota_zero_pair {X : SSet.{u}} {d : ℕ}
    (y : X.obj (Opposite.op ⦋d⦌))
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌))
    (ht : t ∈ (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).obj
      (Opposite.op ⦋d⦌)) :
    (⟨y, (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app
        (Opposite.op ⦋d⦌)) ⟨t, ht⟩)⟩ :
      (X ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌)) =
      SSet.ι₀.app (Opposite.op ⦋d⦌) y := by
  refine Prod.ext rfl ?_
  dsimp only
  change t = _
  ext a
  have ht0 : ∀ a, t a = (0 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  simp only [ht0]
  congr 1

omit [KanComplex F] in
/-- The face inclusion followed by the projection is the face-subcomplex
inclusion. Proved by injectivity of the boundary inclusion: both sides land
in the face `{k}ᶜ` the same way, chasing through `faceInclBd_ι`, the face iso
laws, and `fromPreimage_ι`. -/
private theorem faceInclBd_inv_apply (m : ℕ) (k : Fin (m + 2))
    {d : ℕ} (x : ((faceSubBd m k : SSet.{u})).obj (Opposite.op ⦋d⦌)) :
    (faceInclBd m k).app _ ((faceSubBdInv m k).app _ x) =
      (faceSubBd m k).ι.app _ x := by
  obtain ⟨a, ha⟩ := x
  have key : ((SSet.boundary (m + 1)).ι.app _ ((faceInclBd m k).app _
      ((faceSubBdInv m k).app _ ⟨a, ha⟩))) =
      ((SSet.boundary (m + 1)).ι.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩)) := by
    calc ((SSet.boundary (m + 1)).ι.app _ ((faceInclBd m k).app _
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)))
        = (((faceInclBd m k ≫ (SSet.boundary (m + 1)).ι).app _)
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := rfl
      _ = (((SSet.stdSimplex.δ k).app _)
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [faceInclBd_ι m k]
      _ = (((((SSet.stdSimplex.faceSingletonComplIso k).hom ≫
            (SSet.stdSimplex.face {k}ᶜ).ι).app _))
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            (((SSet.stdSimplex.faceSingletonComplIso k).hom).app _
              (((SSet.stdSimplex.faceSingletonComplIso k).inv).app _
                ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                  (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩)))) := rfl
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            (((((SSet.stdSimplex.faceSingletonComplIso k).inv ≫
              (SSet.stdSimplex.faceSingletonComplIso k).hom).app _))
              ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩))) := rfl
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩)) := by
          rw [Iso.inv_hom_id]
          rfl
      _ = (((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι ≫
            (SSet.stdSimplex.face {k}ᶜ).ι).app _) ⟨a, ha⟩) := rfl
      _ = ((((Subcomplex.preimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι).ι ≫
            (SSet.boundary (m + 1)).ι).app _) ⟨a, ha⟩) := by
          rw [Subcomplex.fromPreimage_ι]
      _ = ((SSet.boundary (m + 1)).ι.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩)) :=
          rfl
  exact SetCoe.ext key

/-- Agreement for the second homotopy extension: on the face–`{0}` corner,
the constant boundary map meets the transplanted face homotopy, since
`{0}`-pairs are `ι₀`-images, the first lift starts at `fk`, and the face
inclusion is a retraction section over the face subcomplex. -/
private theorem agree2 (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((faceSubBd m k).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ s) =
      (((faceSubBd m k : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)) := by
  ext N ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, N = Opposite.op ⦋d⦌ := ⟨N.unop.len, rfl⟩
  have hpair : (⟨(faceSubBdInv m k).app _ ⟨a, ha⟩,
      (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _)
        ⟨t, ht⟩)⟩ :
      (((Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌))) =
      SSet.ι₀.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) :=
    iota_zero_pair _ _ _
  have hH0 : ((((faceSubBd m k : SSet.{u}) ◁
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
      ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
      ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) := by
    calc ((((faceSubBd m k : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = (lift1 m fk c hbc).app _
          (⟨(faceSubBdInv m k).app _ ⟨a, ha⟩,
            (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _)
              ⟨t, ht⟩)⟩) := rfl
      _ = (lift1 m fk c hbc).app _
          (SSet.ι₀.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [hpair]
      _ = (SSet.ι₀ ≫ lift1 m fk c hbc).app _
          ((faceSubBdInv m k).app _ ⟨a, ha⟩) := rfl
      _ = fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) := by
          rw [lift1_zero m fk c hbc]
  have hgoal : ((((faceSubBd m k).ι ▷
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ s)).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      ((((faceSubBd m k : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := by
    calc ((((faceSubBd m k).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) :
          SSet.{u})) ≫
        (fst _ _ ≫ s)).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = s.app _ a := rfl
      _ = s.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩) := rfl
      _ = s.app _ ((faceInclBd m k).app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [faceInclBd_inv_apply m k ⟨a, ha⟩]
      _ = ((faceInclBd m k ≫ s).app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := rfl
      _ = (fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by rw [← hfk]
      _ = ((((faceSubBd m k : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
          ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
          ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := hH0.symm
  exact hgoal

/-- Glued map on the `{0}`-cap prism over the boundary: the constant boundary
map on the base side, the transplanted face homotopy on the face side. -/
private noncomputable def gBd1 (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u})) ⟶ F :=
  (Subcomplex.unionProd.isPushout (faceSubBd m k)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ s)
    ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)
    (agree2 m k fk c hbc s hfk)

omit [KanComplex F] in
/-- The `{0}`-cap prism over the boundary is anodyne, by pushout-product. -/
private theorem capBd_mem_anodyne (m : ℕ) (k : Fin (m + 2)) :
    SSet.anodyneExtensions (((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι) :=
  SSet.anodyneExtensions_unionProd_ι _ _ faceZero_mem_anodyne

/-- Second homotopy extension: the glued cap map extends over
`∂Δ[m + 1] ⊗ Δ[1]`. -/
private noncomputable def liftBd (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (∂Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gBd1 m k fk c hbc s hfk)
    (capBd_mem_anodyne m k)).choose

private theorem liftBd_spec (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      liftBd m k fk c hbc s hfk) = gBd1 m k fk c hbc s hfk :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gBd1 m k fk c hbc s hfk)
    (capBd_mem_anodyne m k)).choose_spec

/-- The second extension starts at the original boundary map. -/
private theorem liftBd_zero (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.ι₀ ≫ liftBd m k fk c hbc s hfk = s := by
  have hg := (Subcomplex.unionProd.isPushout (faceSubBd m k)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inl_desc
    (fst _ _ ≫ s)
    ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)
    (agree2 m k fk c hbc s hfk)
  exact iota_zero_of_lift _ _ _ _ hg (liftBd_spec m k fk c hbc s hfk)

/-- The modified boundary map: restriction of the second extension to `{1}`.
Its selected face is the constant-ridge face `fk'`. -/
private noncomputable def bdFaceFix (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) : (∂Δ[m + 1] : SSet.{u}) ⟶ F :=
  SSet.ι₁ ≫ liftBd m k fk c hbc s hfk

/-- The modified boundary map carries exactly the corrected face on the nose. -/
private theorem face_fix_eq (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk = fk' m fk c hbc := by
  have hH : faceSubBdHom m k ≫ (faceSubBd m k).ι = faceInclBd m k := rfl
  have hside : ((faceSubBd m k).ι ▷ (Δ[1] : SSet.{u})) ≫
      liftBd m k fk c hbc s hfk =
      (faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc := by
    rw [← Subcomplex.unionProd.ι₂_ι (faceSubBd m k)
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, liftBd_spec m k fk c hbc s hfk]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  have e1 : (faceInclBd m k ▷ (Δ[1] : SSet.{u})) =
      (faceSubBdHom m k ▷ (Δ[1] : SSet.{u})) ≫
        ((faceSubBd m k).ι ▷ (Δ[1] : SSet.{u})) := by
    rw [← hH]
    exact comp_whiskerRight _ _ _
  have e2 : (faceSubBdHom m k ▷ (Δ[1] : SSet.{u})) ≫
      ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc) =
      lift1 m fk c hbc := by
    rw [← Category.assoc, ← comp_whiskerRight, faceSubBd_hom_inv,
      id_whiskerRight, Category.id_comp]
  calc faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk
      = faceInclBd m k ≫ (SSet.ι₁ ≫ liftBd m k fk c hbc s hfk) := rfl
    _ = SSet.ι₁ ≫ ((faceInclBd m k ▷ (Δ[1] : SSet.{u})) ≫
          liftBd m k fk c hbc s hfk) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₁_comp]
    _ = SSet.ι₁ ≫ lift1 m fk c hbc := by
        rw [e1, Category.assoc, hside]
        exact congrArg (SSet.ι₁ ≫ ·) e2

/-- The ridge-to-horn map followed into the boundary equals the boundary
inclusion of the face inclusion: both land as `δ k` after the boundary
inclusion, so they agree by cancellation. -/
private theorem ridge_eq (m : ℕ) (k : Fin (m + 2)) :
    ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k) =
      (SSet.boundary m).ι ≫ faceInclBd m k := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  have hle : Subcomplex.homOfLE (horn_le_boundary k) ≫
        (SSet.boundary (m + 1)).ι = (SSet.horn (m + 1) k).ι :=
    Subcomplex.homOfLE_ι _
  calc (ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          (SSet.boundary (m + 1)).ι
      = ridgeToHorn m k ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          (SSet.boundary (m + 1)).ι) := Category.assoc _ _ _
    _ = ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι :=
        congrArg (ridgeToHorn m k ≫ ·) hle
    _ = (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k := ridgeToHorn_spec m k
    _ = (SSet.boundary m).ι ≫
          (faceInclBd m k ≫ (SSet.boundary (m + 1)).ι) :=
        congrArg ((SSet.boundary m).ι ≫ ·) (faceInclBd_ι m k).symm
    _ = ((SSet.boundary m).ι ≫ faceInclBd m k) ≫ (SSet.boundary (m + 1)).ι :=
        (Category.assoc _ _ _).symm

/-- The horn filler's distinguished face has constant ridge, at the same
last-vertex value as `fk'`: chase the ridge through the horn into `s'`,
then through the face inclusion into `fk'`. -/
private theorem hornFace_const (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (SSet.boundary m).ι ≫
        (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have hspec := hornFill_spec k (bdFaceFix m k fk c hbc s hfk)
  have e1 : (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k =
      ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι := (ridgeToHorn_spec m k).symm
  calc (SSet.boundary m).ι ≫
          (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
      = ((SSet.boundary m).ι ≫ SSet.stdSimplex.δ k) ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk) :=
        (Category.assoc _ _ _).symm
    _ = (ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι) ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk) :=
        congrArg (· ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) e1
    _ = ridgeToHorn m k ≫ ((SSet.horn (m + 1) k).ι ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk)) :=
        Category.assoc _ _ _
    _ = ridgeToHorn m k ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          bdFaceFix m k fk c hbc s hfk) :=
        congrArg (ridgeToHorn m k ≫ ·) hspec.symm
    _ = (ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          bdFaceFix m k fk c hbc s hfk := (Category.assoc _ _ _).symm
    _ = ((SSet.boundary m).ι ≫ faceInclBd m k) ≫
          bdFaceFix m k fk c hbc s hfk :=
        congrArg (· ≫ bdFaceFix m k fk c hbc s hfk) (ridge_eq m k)
    _ = (SSet.boundary m).ι ≫ (faceInclBd m k ≫
          bdFaceFix m k fk c hbc s hfk) := Category.assoc _ _ _
    _ = (SSet.boundary m).ι ≫ fk' m fk c hbc :=
        congrArg ((SSet.boundary m).ι ≫ ·)
          (face_fix_eq m k fk c hbc s hfk)
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) :=
        fk'_ridge m fk c hbc

omit [KanComplex F] in
/-- A simplex with constant ridge is a pointed simplex. -/
private noncomputable def facePt {m : ℕ} (g : (Δ[m] : SSet.{u}) ⟶ F)
    (y : F _⦋0⦌) (h : (SSet.boundary m).ι ≫ g = SSet.const y) :
    F.PtSimplex m y where
  map := g
  comm := by
    have hRHS : ∀ (X : SSet.{u}) (z : F _⦋0⦌),
        (SSet.const (X := X) (⟨z, SSet.Subcomplex.mem_ofSimplex_obj z⟩ :
          (SSet.Subcomplex.ofSimplex z : SSet.{u}) _⦋0⦌) ≫
        (SSet.Subcomplex.ofSimplex z).ι) = SSet.const (X := X) z := by
      intro X z
      ext a b
      rfl
    rw [hRHS]
    exact h

/-- A pointed homotopy yields a rel-boundary homotopy between the underlying
maps: stationarity on the boundary is the relative `rel` law read
pointwise, transported along the pointed `comm` law. -/
private noncomputable def homotopyRelOfPt {m : ℕ} {y : F _⦋0⦌}
    {p q : F.PtSimplex m y} (H : p.Homotopy q) :
    SSet.HomotopyRel p.map q.map (SSet.boundary m) where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  stationary := fun x hx t => by
    have hpt : H.h.app _ ⟨x, t⟩ =
        (((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h).app _
          ⟨⟨x, hx⟩, t⟩) := rfl
    have hbase : p.map.app _ x =
        ((((SSet.boundary m).ι ≫ p.map).app _)) ⟨x, hx⟩ := rfl
    have hrel := congrArg (fun ψ :
        (((SSet.boundary m : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶ F) =>
        ψ.app _ ⟨⟨x, hx⟩, t⟩) H.rel
    have hcomm := congrArg (fun ψ : (((SSet.boundary m : SSet.{u})) ⟶ F) =>
      ψ.app _ ⟨x, hx⟩) p.comm
    rw [hpt, hrel]
    exact hcomm.symm.trans (by rfl)

/-- The rel-boundary homotopy from the horn filler's distinguished face to
the true face: both package as pointed simplices at the last-vertex value,
which `π` subsingletonness identifies. -/
private noncomputable def correctionH (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.HomotopyRel (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
      (fk' m fk c hbc) (SSet.boundary m) :=
  show SSet.HomotopyRel
    (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
    (fk' m fk c hbc) (SSet.boundary m) from
  homotopyRelOfPt (SSet.PtSimplex.RelStruct₀.homotopy
    (π.mk_eq_mk_iff.mp ((hπ m
      (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m)))).elim
      (π.mk (facePt _ _ (hornFace_const m k fk c hbc s hfk)))
      (π.mk (facePt _ _ (fk'_ridge m fk c hbc))))).some)

/-- Correcting the horn filler's distinguished face to the true face: the
accepted provider swaps in `fk'` while freezing every other face. -/
private noncomputable def correctedFace (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) : (Δ[m + 1] : SSet.{u}) ⟶ F :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose

private theorem correctedFace_face (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.stdSimplex.δ k ≫ correctedFace m k hπ fk c hbc s hfk =
      fk' m fk c hbc :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose_spec.1

private theorem correctedFace_other (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) (j : Fin (m + 2)) (hjk : j ≠ k) :
    SSet.stdSimplex.δ j ≫ correctedFace m k hπ fk c hbc s hfk =
      SSet.stdSimplex.δ j ≫ hornFill k (bdFaceFix m k fk c hbc s hfk) :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose_spec.2 j hjk

/-- The face inclusion is the boundary face map: both project to `δ k`. -/
private theorem faceInclBd_eq (m : ℕ) (k : Fin (m + 2)) :
    faceInclBd m k = SSet.boundary.ι k := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  rw [faceInclBd_ι m k]
  exact (SSet.boundary.ι_ι k).symm

/-- A non-distinguished face factors through the horn into the boundary face
map: both project to `δ j`. -/
private theorem hornFaceIncl_eq (m : ℕ) (k : Fin (m + 2)) (j : Fin (m + 2))
    (hjk : j ≠ k) :
    SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k) =
      SSet.boundary.ι j := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  have hle : Subcomplex.homOfLE (horn_le_boundary k) ≫
        (SSet.boundary (m + 1)).ι = (SSet.horn (m + 1) k).ι :=
    Subcomplex.homOfLE_ι _
  calc (SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          (SSet.boundary (m + 1)).ι
      = SSet.horn.ι k j hjk ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          (SSet.boundary (m + 1)).ι) := Category.assoc _ _ _
    _ = SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι :=
        congrArg (SSet.horn.ι k j hjk ≫ ·) hle
    _ = SSet.stdSimplex.δ j := SSet.horn.ι_ι _ _ _
    _ = SSet.boundary.ι j ≫ (SSet.boundary (m + 1)).ι :=
        (SSet.boundary.ι_ι j).symm

/-- The corrected simplex extends the modified boundary map: on the
distinguished face this is the provider correction plus `face_fix_eq`; on
every other face the provider freezes the horn filler, which restricts
through the horn to `s'`. -/
private theorem correctedFace_extends (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (SSet.boundary (m + 1)).ι ≫ correctedFace m k hπ fk c hbc s hfk =
      bdFaceFix m k fk c hbc s hfk := by
  refine SSet.boundary.hom_ext (fun j => ?_)
  by_cases hjk : j = k
  · rw [hjk]
    have hface := correctedFace_face m k hπ fk c hbc s hfk
    calc SSet.boundary.ι k ≫ ((SSet.boundary (m + 1)).ι ≫
            correctedFace m k hπ fk c hbc s hfk)
        = SSet.stdSimplex.δ k ≫ correctedFace m k hπ fk c hbc s hfk := by
          rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = fk' m fk c hbc := hface
      _ = faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk :=
          (face_fix_eq m k fk c hbc s hfk).symm
      _ = SSet.boundary.ι k ≫ bdFaceFix m k fk c hbc s hfk :=
          congrArg (· ≫ bdFaceFix m k fk c hbc s hfk) (faceInclBd_eq m k)
  · have hother := correctedFace_other m k hπ fk c hbc s hfk j hjk
    have hspec := hornFill_spec k (bdFaceFix m k fk c hbc s hfk)
    have hδ : SSet.stdSimplex.δ j =
        SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι :=
      (SSet.horn.ι_ι k j hjk).symm
    calc SSet.boundary.ι j ≫ ((SSet.boundary (m + 1)).ι ≫
            correctedFace m k hπ fk c hbc s hfk)
        = SSet.stdSimplex.δ j ≫ correctedFace m k hπ fk c hbc s hfk := by
          rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = SSet.stdSimplex.δ j ≫ hornFill k (bdFaceFix m k fk c hbc s hfk) :=
          hother
      _ = (SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι) ≫
            hornFill k (bdFaceFix m k fk c hbc s hfk) :=
          congrArg (· ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) hδ
      _ = SSet.horn.ι k j hjk ≫ ((SSet.horn (m + 1) k).ι ≫
            hornFill k (bdFaceFix m k fk c hbc s hfk)) :=
          Category.assoc _ _ _
      _ = SSet.horn.ι k j hjk ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
            bdFaceFix m k fk c hbc s hfk) :=
          congrArg (SSet.horn.ι k j hjk ≫ ·) hspec.symm
      _ = (SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
            bdFaceFix m k fk c hbc s hfk := (Category.assoc _ _ _).symm
      _ = SSet.boundary.ι j ≫ bdFaceFix m k fk c hbc s hfk :=
          congrArg (· ≫ bdFaceFix m k fk c hbc s hfk)
            (hornFaceIncl_eq m k j hjk)

omit [KanComplex F] in
/-- A pair with `{1}`-second component equals the `ι₁` image of its first
component. Mirror of `iota_zero_pair`. -/
private theorem iota_one_pair {X : SSet.{u}} {d : ℕ}
    (y : X.obj (Opposite.op ⦋d⦌))
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌))
    (ht : t ∈ (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).obj
      (Opposite.op ⦋d⦌)) :
    (⟨y, (((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app
        (Opposite.op ⦋d⦌)) ⟨t, ht⟩)⟩ :
      (X ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌)) =
      SSet.ι₁.app (Opposite.op ⦋d⦌) y := by
  refine Prod.ext rfl ?_
  dsimp only
  change t = _
  ext a
  have ht1 : ∀ a, t a = (1 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  simp only [ht1]
  congr 1

/-- Agreement for the capped-prism transport: the constant corrected filler
on the top side meets the boundary homotopy on the boundary side, since
`{1}`-pairs are `ι₁`-images, the homotopy ends at `s'`, and the corrected
simplex extends `s'`. -/
private theorem agreeCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((SSet.boundary (m + 1)).ι ▷
        ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk) =
      (((∂Δ[m + 1] : SSet.{u}) ◁
          (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        liftBd m k fk c hbc s hfk) := by
  ext n ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have hpair : (⟨⟨a, ha⟩, ((SSet.stdSimplex.face {1} :
      (Δ[1] : SSet.{u}).Subcomplex).ι.app _ ⟨t, ht⟩)⟩ :
      ((((∂Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
        (Opposite.op ⦋d⦌)))) =
      SSet.ι₁.app _ (⟨a, ha⟩ : ((∂Δ[m + 1] : SSet.{u}).obj
        (Opposite.op ⦋d⦌))) :=
    iota_one_pair (X := (∂Δ[m + 1] : SSet.{u})) (d := d)
      (⟨a, ha⟩ : ((∂Δ[m + 1] : SSet.{u}).obj (Opposite.op ⦋d⦌))) t ht
  have hH1 : (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
      ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
        ⟨t, ht⟩)⟩ =
      (bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩ := by
    calc (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
            ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
              ⟨t, ht⟩)⟩
        = (liftBd m k fk c hbc s hfk).app _
            (SSet.ι₁.app _ ⟨a, ha⟩) := by rw [← hpair]
      _ = (SSet.ι₁ ≫ liftBd m k fk c hbc s hfk).app _ ⟨a, ha⟩ := rfl
      _ = (bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩ := rfl
  have hgoal : ((((SSet.boundary (m + 1)).ι ▷
      ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)).app _
      ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      ((((∂Δ[m + 1] : SSet.{u}) ◁
        (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := by
    calc ((((SSet.boundary (m + 1)).ι ▷
        ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
        (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = (correctedFace m k hπ fk c hbc s hfk).app _ a := rfl
      _ = (((SSet.boundary (m + 1)).ι ≫
          correctedFace m k hπ fk c hbc s hfk).app _ ⟨a, ha⟩) := rfl
      _ = ((bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩) := by
          rw [correctedFace_extends m k hπ fk c hbc s hfk]
      _ = (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
          ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩ := hH1.symm
      _ = _ := rfl
  exact hgoal

/-- Glued map on the `{1}`-capped prism: the constant corrected filler on
the top side, the boundary homotopy on the boundary side. -/
private noncomputable def gCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((capSubcomplex (m + 1)) : SSet.{u})) ⟶ F :=
  (Subcomplex.unionProd.isPushout (SSet.boundary (m + 1))
    (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)
    (liftBd m k fk c hbc s hfk)
    (agreeCap m k hπ fk c hbc s hfk)

/-- Capped-prism extension: the glued map extends over `Δ[m + 1] ⊗ Δ[1]`. -/
private noncomputable def liftCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant
    (gCap m k hπ fk c hbc s hfk) (cap_mem_anodyneExtensions (m + 1))).choose

private theorem liftCap_spec (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((SSet.boundary (m + 1)).unionProd
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      liftCap m k hπ fk c hbc s hfk) =
      gCap m k hπ fk c hbc s hfk :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant
    (gCap m k hπ fk c hbc s hfk) (cap_mem_anodyneExtensions (m + 1))).choose_spec

/-- The bottom of the capped prism fills the original sphere: restrict the
extension at `ι₀`, where the boundary side is the homotopy starting at `s`. -/
private theorem fillerOfCorrected (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ∃ t : (Δ[m + 1] : SSet.{u}) ⟶ F, (SSet.boundary (m + 1)).ι ≫ t = s := by
  refine ⟨SSet.ι₀ ≫ liftCap m k hπ fk c hbc s hfk, ?_⟩
  have hside : ((SSet.boundary (m + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫
      liftCap m k hπ fk c hbc s hfk = liftBd m k fk c hbc s hfk := by
    rw [← Subcomplex.unionProd.ι₂_ι (SSet.boundary (m + 1))
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, liftCap_spec m k hπ fk c hbc s hfk]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  calc (SSet.boundary (m + 1)).ι ≫
          (SSet.ι₀ ≫ liftCap m k hπ fk c hbc s hfk)
      = SSet.ι₀ ≫ (((SSet.boundary (m + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫
          liftCap m k hπ fk c hbc s hfk) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₀_comp]
    _ = SSet.ι₀ ≫ liftBd m k fk c hbc s hfk :=
        congrArg (SSet.ι₀ ≫ ·) hside
    _ = s := liftBd_zero m k fk c hbc s hfk

/-- Induction step `A(m) → A(m + 1)`: fill the ridge of the chosen face by
the induction hypothesis, then transport the corrected filler back along
the boundary homotopy through the capped prism. -/
private theorem stepAux (m : ℕ)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (IH : ∀ s : (∂Δ[m] : SSet.{u}) ⟶ F,
      ∃ t : Δ[m] ⟶ F, (SSet.boundary m).ι ≫ t = s)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F) :
    ∃ t : (Δ[m + 1] : SSet.{u}) ⟶ F, (SSet.boundary (m + 1)).ι ≫ t = s := by
  obtain ⟨k⟩ : Nonempty (Fin (m + 2)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨c, hc⟩ := IH ((SSet.boundary m).ι ≫ faceInclBd m k ≫ s)
  exact fillerOfCorrected m k hπ (faceInclBd m k ≫ s) c hc s rfl

/-- All-dimensional fillers by ordinary induction from dimension zero. -/
private theorem existsFillerAux (x₀ : F _⦋0⦌)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x)) : ∀ (n : ℕ)
    (s : (∂Δ[n] : SSet.{u}) ⟶ F),
    ∃ t : Δ[n] ⟶ F, (SSet.boundary n).ι ≫ t = s := by
  intro n
  induction n with
  | zero => intro s; exact filler_zero x₀ s
  | succ m IHm => intro s; exact stepAux m hπ IHm s

/-- Every boundary sphere in a weakly contractible Kan complex extends over
the simplex: given a basepoint `x₀` with `π n F x` a subsingleton for every
`n` and every basepoint `x`, each `s : ∂Δ[n] ⟶ F` admits `t : Δ[n] ⟶ F` with
`(boundary n).ι ≫ t = s` (boundary inclusion on the left, filler on the
right). This does not itself establish an `I.rlp` characterization or a
model-category instance. -/
theorem exists_boundary_filler_of_subsingleton_pi (x₀ : F _⦋0⦌)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    {n : ℕ} (s : (∂Δ[n] : SSet.{u}) ⟶ F) :
    ∃ t : Δ[n] ⟶ F, (SSet.boundary n).ι ≫ t = s :=
  existsFillerAux x₀ hπ n s

end SSet.KanComplex
