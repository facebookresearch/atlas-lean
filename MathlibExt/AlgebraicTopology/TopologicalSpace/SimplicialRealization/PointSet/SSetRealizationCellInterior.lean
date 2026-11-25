/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.Analysis.Convex.StdSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationStdSimplex
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.BoundaryProductFace
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import Mathlib.Topology.Order

/-!
# Realized standard-simplex open cell

For `n : ℕ`, the positive-coordinate open-cell locus in
`StdSimplex ℝ (Fin (n + 1))` and its identification with the complement of the
realized-boundary range under `SSet.stdSimplex.toTopIso`, covering both
positive-dimensional simplices and the `n = 0` (`∂Δ[0] = ⊥`) base case.
Consumes `SSet.stdSimplex.toTopIso`,
`SSet.boundaryProductFace.exists_face_cover`,
`SSet.boundary.singleton_face_coord_zero`,
`Convexity.StdSimplex.mem_range_map_iff`,
`SSet.stdSimplex.faceSingletonComplIso` and its `hom_ι` law,
`SSet.face_singleton_compl_le_boundary` with `SSet.Subcomplex.homOfLE_ι`,
`SimplexCategory.toTopHomeo` and its naturality, and
`Convexity.StdSimplex.continuous_weights_apply` for the openness corollary, plus
`SSet.boundary_zero`, `Convexity.StdSimplex` uniqueness
(`weights_apply_eq_one`), and the initial-object bridge
(`SSet.Subcomplex.isInitialBot`, `TopCat.isInitialPEmpty`) for the `n = 0` case.
Mathematical source: standard affine simplex description, cf. Goerss--Jardine,
*Simplicial Homotopy Theory*, Chapter I, §1; simplicial boundary ▷ faces via
the pinned `SSet.boundary` APIs.

Nonclaims: no unique cell carrier, no compact-subset finite-support theorem,
no arbitrary product, no fibration or model-category result. The `IsOpen`
corollary is included only because it follows directly from coordinate
continuity.
-/

@[expose] public section

open CategoryTheory

universe u

open scoped Simplicial

namespace SSet

namespace realizationCellInterior

/-- Positive-coordinate open-cell locus in the topological standard simplex. -/
def openCell (n : ℕ) : Set (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  {t | ∀ i, 0 < t.weights i}

/-- The open-cell locus is open: a finite intersection of `Ioi` preimages
under the continuous coordinate evaluations. -/
theorem openCell_isOpen (n : ℕ) : IsOpen (openCell n) := by
  have hEq : openCell n =
      ⋂ i, (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => t.weights i) ⁻¹' Set.Ioi 0 := by
    ext t
    simp [openCell, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
  rw [hEq]
  exact isOpen_iInter_of_finite fun i =>
    IsOpen.preimage (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i) isOpen_Ioi

/-- The `toTopIso` preimage of the open cell is the complement of the realized
boundary range. Smallest useful form: positive-dimensional simplices only,
where `exists_face_cover` and `singleton_face_coord_zero` apply. -/
theorem toTopIso_preimage_openCell_compl_range (n : ℕ) :
    (SSet.stdSimplex.toTopIso (SimplexCategory.mk (n + 1))).hom ⁻¹' openCell (n + 1) =
      (Set.range ⇑(SSet.toTop.map (SSet.boundary (n + 1)).ι))ᶜ := by
  classical
  have hI : ∀ z, (SSet.stdSimplex.toTopIso (SimplexCategory.mk (n + 1))).hom z =
      SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) z := fun z => rfl
  ext y
  constructor
  · intro hy
    rw [Set.mem_compl_iff]
    intro hr
    obtain ⟨x, hx⟩ := hr
    obtain ⟨i, p, hp⟩ := SSet.boundaryProductFace.exists_face_cover n x
    have hMor : SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι =
        SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) ≫
          SSet.toTop.map (SSet.boundary (n + 1)).ι := by
      rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
    have hPt : ⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι) p = y := by
      have h1 := ConcreteCategory.congr_hom hMor p
      simpa [CategoryTheory.comp_apply, hp, hx] using h1
    have hMem : (SSet.stdSimplex.toTopIso (SimplexCategory.mk (n + 1))).hom y ∈
        openCell (n + 1) := hy
    simp only [openCell, Set.mem_ofPred_eq] at hMem
    have hEqY : (SSet.stdSimplex.toTopIso (SimplexCategory.mk (n + 1))).hom y =
        SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y := hI y
    rw [hEqY] at hMem
    have hZero := SSet.boundary.singleton_face_coord_zero (n := n) i p
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y) (by rw [hPt])
    exact (ne_of_lt (hMem i)) hZero.symm
  · intro hC
    rw [Set.mem_compl_iff] at hC
    rw [Set.mem_preimage]
    have hEqY : (SSet.stdSimplex.toTopIso (SimplexCategory.mk (n + 1))).hom y =
        SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y := hI y
    simp only [openCell, Set.mem_ofPred_eq]
    intro i
    rw [hEqY]
    by_contra hCon
    have hNonneg : 0 ≤ (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y).weights i :=
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y).weights_nonneg i
    have hZeroI : (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y).weights i = 0 :=
      le_antisymm (le_of_not_gt hCon) hNonneg
    have hFaceMem : (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) y) ∈
        Set.range (Convexity.StdSimplex.map (Fin.succAbove i)) := by
      rw [Convexity.StdSimplex.mem_range_map_iff]
      intro a ha
      have hai : a = i := by
        by_contra hne
        apply ha
        obtain ⟨z, hz⟩ := (Fin.exists_succAbove_eq_iff).mpr hne
        exact ⟨z, hz⟩
      rw [hai]
      exact hZeroI
    obtain ⟨v, hv⟩ := hFaceMem
    let Hn := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
    obtain ⟨q, hq⟩ : ∃ q : SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk n)),
        Hn q = v :=
      ⟨Hn.symm v, Hn.apply_symm_apply v⟩
    let e := SSet.stdSimplex.faceSingletonComplIso (n := n) i
    have hEq : (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι =
        e.inv ≫ SSet.stdSimplex.δ (n := n) i := by
      calc (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι
          = e.inv ≫ e.hom ≫ (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι := by simp
        _ = e.inv ≫ SSet.stdSimplex.δ (n := n) i := by
            rw [SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    have hEqTop : SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι =
        SSet.toTop.map e.inv ≫ SSet.toTop.map (SSet.stdSimplex.δ (n := n) i) := by
      rw [hEq, Functor.map_comp]
    have hInv : SSet.toTop.map e.inv (SSet.toTop.map e.hom q) = q := by
      have hMorIso : SSet.toTop.map e.hom ≫ SSet.toTop.map e.inv = 𝟙 _ := by
        simp only [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
      have h1 := ConcreteCategory.congr_hom hMorIso q
      rw [CategoryTheory.comp_apply] at h1
      exact h1
    have hNat : (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))
        (⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i)) (SSet.toTop.map e.inv
          (SSet.toTop.map e.hom q))) =
        (Convexity.StdSimplex.map (Fin.succAbove i))
          (SimplexCategory.toTopHomeo (SimplexCategory.mk n)
            (SSet.toTop.map e.inv (SSet.toTop.map e.hom q))) := by
      have h2 : (⇑(SimplexCategory.δ (n := n) i) : Fin (n + 1) → Fin (n + 2)) =
          Fin.succAbove i := rfl
      have hN := SimplexCategory.toTopHomeo_naturality_apply
        (f := SimplexCategory.δ (n := n) i)
        (SSet.toTop.map e.inv (SSet.toTop.map e.hom q))
      rw [h2] at hN
      exact hN
    have hKey : (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))
        (⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι)
          (SSet.toTop.map e.hom q)) =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) y := by
      have hF : ⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι)
            (SSet.toTop.map e.hom q) =
          ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i))
            (SSet.toTop.map e.inv (SSet.toTop.map e.hom q)) := by
        have h1 := ConcreteCategory.congr_hom hEqTop (SSet.toTop.map e.hom q)
        simpa [CategoryTheory.comp_apply] using h1
      rw [hF, hInv]
      have hNat2 := hNat
      rw [hInv, hq] at hNat2
      rw [hNat2, hv]
    have hFaceY : ⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι)
          (SSet.toTop.map e.hom q) = y :=
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).injective hKey
    have hB : y ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary (n + 1)).ι) :=
      ⟨SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i))
        (SSet.toTop.map e.hom q), by
        have hMor2 : SSet.toTop.map
              (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) ≫
            SSet.toTop.map (SSet.boundary (n + 1)).ι =
            SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι := by
          rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
        have h2 := ConcreteCategory.congr_hom hMor2 (SSet.toTop.map e.hom q)
        simpa [CategoryTheory.comp_apply, hFaceY] using h2⟩
    exact hC hB

/-- The `n = 0` base case: the `toTopIso` preimage of the open cell is the
complement of the realized-boundary range. Since `∂Δ[0] = ⊥`
(`SSet.boundary_zero`), the range is empty: the domain is initial, hence empty
via `TopCat.isInitialPEmpty`. The preimage is everything because the
topological `0`-simplex is a singleton (`Convexity.StdSimplex`
uniqueness). -/
theorem toTopIso_preimage_openCell_compl_range_zero :
    (SSet.stdSimplex.toTopIso (SimplexCategory.mk 0)).hom ⁻¹' openCell 0 =
      (Set.range ⇑(SSet.toTop.map (SSet.boundary 0).ι))ᶜ := by
  have hB : SSet.boundary 0 = ⊥ := SSet.boundary_zero
  have hInitSSet : CategoryTheory.Limits.IsInitial ((SSet.boundary 0 : SSet)) := by
    rw [hB]
    exact SSet.Subcomplex.isInitialBot
  have hInitTop :
      CategoryTheory.Limits.IsInitial (SSet.toTop.obj (SSet.boundary 0 : SSet)) :=
    hInitSSet.isInitialObj (G := SSet.toTop)
  have hIso : SSet.toTop.obj (SSet.boundary 0 : SSet) ≅ (TopCat.of PEmpty : TopCat) :=
    hInitTop.uniqueUpToIso TopCat.isInitialPEmpty
  have hElim : ∀ x : SSet.toTop.obj (SSet.boundary 0 : SSet), False :=
    fun x => PEmpty.elim ((TopCat.homeoOfIso hIso) x)
  have hRange : Set.range ⇑(SSet.toTop.map (SSet.boundary 0).ι) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    exact hElim x
  have hOpen : openCell 0 = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    simp only [openCell, Set.mem_ofPred_eq]
    intro i
    have : Subsingleton (Fin (0 + 1)) := by rw [zero_add]; infer_instance
    have h1 : t.weights i = 1 := Convexity.StdSimplex.weights_apply_eq_one t i
    rw [h1]
    norm_num
  have hPre :
      (SSet.stdSimplex.toTopIso (SimplexCategory.mk 0)).hom ⁻¹' openCell 0 = Set.univ := by
    rw [hOpen, Set.preimage_univ]
  rw [hRange, Set.compl_empty]
  exact hPre

end realizationCellInterior

/-!
# Interior (open-cell) presentation for realized points (4.34.1)

Prerequisite for the zero-fiber support-reduction route, ported to
`Convexity.StdSimplex` with `.weights`.
Every point of `SSet.toTop.obj T` has a presentation by a realized
standard simplex at a strictly-positive (interior) point.

Reuse map (4.34.1):
* `SSet.exists_nonDegenerate_toTop_presentation` for the initial
  (arbitrary-coordinate) presentation;
* `SimplexCategory.toTopHomeo` / `SSet.yonedaEquiv` for the
  simplex/realization transport;
* `Convexity.StdSimplex.fin1_pos` (`MathlibExt/Analysis/Convex/StdSimplex.lean`)
  for the `Fin 1` base case;
* `Convexity.StdSimplex.face_factor_succAbove` (same file) for the single
  zero-coordinate face factor;
* `SimplexCategory.toTopHomeo_symm_naturality_apply`,
  `SSet.stdSimplex.δ` (`= SSet.stdSimplex.map (SimplexCategory.δ _)`),
  and `SSet.stdSimplex.δ_comp_yonedaEquiv_symm` for the one-step
  SSet dimension reduction (same idiom as
  `RealizationBoundaryZeroCoordinate`).

No legacy simplex carrier is restored here: this file uses
`Convexity.StdSimplex`, `.weights`, and `SimplexCategory.toTopHomeo` directly,
so no legacy carrier bridge is needed.
File order: private single-step SSet reduction, public interior existence.
The former private `fin1_pos` / single-step new-simplex factor now live in
`MathlibExt/Analysis/Convex/StdSimplex.lean` and are reused.
Minimal imports only; no new abstraction.

Nonclaims: no `boundary_complement_all` (neither direction is claimed
here beyond the interior existence itself), no density/presentation
duplication, no subdivision, simplicial approximation, Kan filling, fibration,
model-category, or weak-equivalence result, no KQ3 claim, no global
finite-base chart (per blueprint monodromy warning), no
reverse/iff characterization of boundary membership.
Additional files that still mention the legacy simplex carrier
(`SSetRealizationFiberPointSurjective`) keep their one-file scope and need a
separate migration; they are not edited here.
-/

/-- One-step SSet dimension reduction: a presentation whose simplex
coordinate vanishes at `j` factors through the `j`-th face, giving a
presentation in one lower dimension with the same realized image.
Transport follows the `RealizationBoundaryZeroCoordinate`
idiom (`toTopHomeo` naturality + `δ_comp_yonedaEquiv_symm`); no
subdivision, model, or KQ3 input. -/
private theorem exists_openCell_rep {m : ℕ} (T : SSet.{u})
    (s : T _⦋m + 1⦌) (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m + 1⦌))
    (j : Fin (m + 2))
    (hj : ((SimplexCategory.toTopHomeo ⦋m + 1⦌) y).weights j = 0) :
    ∃ (s' : T _⦋m⦌) (y' : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s') y' =
        SSet.toTop.map (SSet.yonedaEquiv.symm s) y := by
  let p : Convexity.StdSimplex ℝ (Fin (m + 2)) :=
    (SimplexCategory.toTopHomeo ⦋m + 1⦌) y
  have hp : p.weights j = 0 := hj
  obtain ⟨q, hq⟩ := Convexity.StdSimplex.face_factor_succAbove p j hp
  have hδ_eq : (SSet.stdSimplex.δ (n := m) j : (Δ[m] : SSet.{u}) ⟶
      (Δ[m + 1] : SSet.{u})) =
      SSet.stdSimplex.map (SimplexCategory.δ (n := m) j) := rfl
  have hcoe : (⇑(SimplexCategory.δ (n := m) j) :
      Fin (m + 1) → Fin (m + 2)) = Fin.succAbove j := rfl
  have hnat := SimplexCategory.toTopHomeo_symm_naturality_apply
    (f := SimplexCategory.δ (n := m) j) (x := q)
  have hsym : (⦋m + 1⦌.toTopHomeo).symm p =
      SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
        ((⦋m⦌.toTopHomeo).symm q) := by
    rw [← hq]
    rw [hδ_eq]
    simpa [hcoe] using hnat
  have hy : y = SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
      ((⦋m⦌.toTopHomeo).symm q) := by
    have h1 : (⦋m + 1⦌.toTopHomeo).symm p = y := by
      simp [p]
    rw [hsym] at h1
    exact h1.symm
  refine ⟨T.δ j s, (⦋m⦌.toTopHomeo).symm q, ?_⟩
  calc SSet.toTop.map (SSet.yonedaEquiv.symm (T.δ j s))
          ((⦋m⦌.toTopHomeo).symm q)
      = SSet.toTop.map (SSet.stdSimplex.δ (n := m) j ≫ SSet.yonedaEquiv.symm s)
          ((⦋m⦌.toTopHomeo).symm q) := by
        rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm s)
          (SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
            ((⦋m⦌.toTopHomeo).symm q)) := by
        rw [Functor.map_comp]
        rfl
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm s) y := by
        rw [← hy]

namespace OpenCell

/-- Every realized point has an interior (strictly-positive-coordinate)
presentation. Minimal-dimension argument: the initial arbitrary
presentation exists by `exists_nonDegenerate_toTop_presentation`;
a minimal-dimension arbitrary presentation must already be interior,
else the one-step reduction above contradicts minimality. The `Fin 1`
case is `fin1_pos`. -/
theorem exists_openCell (T : SSet.{u}) (x : SSet.toTop.obj T) :
    ∃ (n : ℕ) (s : T _⦋n⦌)
      (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x ∧
      ∀ j, 0 < ((SimplexCategory.toTopHomeo ⦋n⦌) y).weights j := by
  classical
  obtain ⟨n₀, s₀, _, y₀, hy₀⟩ :=
    SSet.exists_nonDegenerate_toTop_presentation T x
  have hNe : ∃ n, ∃ (s : T _⦋n⦌)
      (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x :=
    ⟨n₀, s₀, y₀, hy₀⟩
  let N := Nat.find hNe
  have hNdef : N = Nat.find hNe := rfl
  have hNspec := Nat.find_spec hNe
  have hNspecN : ∃ (s : T _⦋N⦌) (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋N⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x := hNspec
  obtain ⟨sN, yN, hyN⟩ := hNspecN
  have hNmin : ∀ m, (∃ (s : T _⦋m⦌)
      (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x) → N ≤ m :=
    fun m hm => Nat.find_min' hNe hm
  refine ⟨N, sN, yN, hyN, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hcon
  have hle : (0 : ℝ) ≤ ((SimplexCategory.toTopHomeo ⦋N⦌) yN).weights j :=
    ((SimplexCategory.toTopHomeo ⦋N⦌) yN).weights_nonneg j
  have hj0 : ((SimplexCategory.toTopHomeo ⦋N⦌) yN).weights j = 0 :=
    le_antisymm hj hle
  clear hj hle
  revert hj0
  revert hyN
  revert j
  revert yN
  revert sN
  cases hEq : N with
  | zero =>
    intro _s0 y0 j0 _hy0 hj00
    have hFind0 : Nat.find hNe = 0 := hNdef ▸ hEq
    have hpos := Convexity.StdSimplex.fin1_pos ((SimplexCategory.toTopHomeo ⦋0⦌) y0) j0
    rw [hj00] at hpos
    exact lt_irrefl 0 hpos
  | succ m =>
    intro sS yS jS hyS hjS
    have hFindS : Nat.find hNe = m + 1 := hNdef ▸ hEq
    obtain ⟨s', y', hy'⟩ :=
      exists_openCell_rep (m := m) (T := T) (s := sS) (y := yS) (j := jS) (hj := hjS)
    have hm : ∃ (s : T _⦋m⦌)
        (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌)),
        SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x := by
      refine ⟨s', y', ?_⟩
      rw [hy', hyS]
    have hle' := hNmin m hm
    omega

end OpenCell

end SSet

end
