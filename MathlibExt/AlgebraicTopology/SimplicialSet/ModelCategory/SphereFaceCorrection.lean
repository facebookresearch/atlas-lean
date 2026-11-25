/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-! # Correcting one face of a simplex along a rel-boundary homotopy

Given `w : Δ[m + 1] ⟶ F` into a Kan complex and a homotopy
`H : HomotopyRel (δ k ≫ w) v (boundary m)` from the `k`-th face of `w`
to `v`, stationary on the boundary `∂Δ[m]`, this module builds
`w' : Δ[m + 1] ⟶ F` with `δ k ≫ w' = v` and all other faces unchanged.

## Homotopy-extension (HEP) argument

Write `B = ∂Δ[m + 1]`, `Hk = Λ[m + 1, k]`, `Fk = face {k}ᶜ` (the image of
`δ k`), so `B = Hk ⊔ Fk` (`sup_horn_face`, via `horn_eq_iSup` and
`boundary_eq_iSup`).

1. **Boundary cylinder side.** On `Hk ⊗ Δ[1]` take the constant homotopy
   `fst ≫ Hk.ι ≫ w` (`gHorn`); on `Fk ⊗ Δ[1]` take the transported
   homotopy `(e.inv ▷ Δ[1]) ≫ H.h` (`gFace`), where
   `e = faceSingletonComplIso k : Δ[m] ≅ Fk`. They agree on
   `(Hk ⊓ Fk) ⊗ Δ[1]` (`agree_inf`): a simplex there lies over
   `∂Δ[m]` under `e.inv` (`face_data`, a `succAbove` range argument),
   where `H` is stationary (`HomotopyRel.stationary`). Gluing along the
   tensored pushout `sqT` (the `BicartSq` `bicart` pushed through
   `_ ⊗ Δ[1]`, which preserves colimits) yields
   `gBd : B ⊗ Δ[1] ⟶ F`.
2. **Prism extension.** Let `R = B.unionProd (face {0}) ≤ Δ[m + 1] ⊗ Δ[1]`.
   Its inclusion is anodyne (`prismR_mem_anodyne`, via
   `anodyneExtensions_unionProd_ι` and `horn_ι`, as in
   `cylinderInclusion_mem_anodyneExtensions`). Glue `fst ≫ w` on
   `Δ[m + 1] ⊗ {0}` (`gZero`) with `gBd` on `B ⊗ Δ[1]`; they agree on
   `B ⊗ {0}` (`agree_prism`: both sides are `w` on `B`, using that
   `{0}`-simplices of `Δ[1]` are constant `0` and `H` starts at
   `δ k ≫ w`). This gives `gR : R ⟶ F`, extended across the anodyne
   inclusion to `Φ : Δ[m + 1] ⊗ Δ[1] ⟶ F` by Kan fibrancy
   (`anodyneExtensions.exists_lift_of_isFibrant`).
3. **Endpoints.** `w' = ι₁ ≫ Φ`. On face `k`, `Φ` restricts through
   `gBd` to `gFace`, whose `ι₁` end is `e.inv ≫ v`, cancelled by
   `e.hom` to `v`. On face `j ≠ k`, which factors through the horn
   (`horn.ι_ι`), `Φ` restricts to the constant `gHorn` side, whose `ι₁`
   end is the original face of `w` (`ι₁_fst`).

## Nonclaims

* No `π`, sphere-filler theorem, `KanComplex.W`, fixed-top lifting, or
  model structure is used: only Kan extension across an anodyne prism
  inclusion plus the supplied homotopy.
* The boundary decomposition `B = Hk ⊔ Fk` is proved from the
  `iSup` presentations; the intersection `Hk ⊓ Fk` is never computed as
  a subcomplex — agreement is proved pointwise via `face_data`.
* `m = 0` needs no special case: then `H` is relative to
  `boundary 0 = ⊥` and the `succAbove` range argument in `face_data`
  still produces the required boundary membership (vacuously, from an
  empty intersection).
-/

@[expose] public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

variable {F : SSet.{u}} {m : ℕ} {k : Fin (m + 2)}

/-- The `k`-th face of `Δ[m + 1]` (complement of `{k}`), the image of `δ k`. -/
private noncomputable def faceSub (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face {k}ᶜ

/-- The `k`-th horn of `Δ[m + 1]`. -/
private noncomputable def hornSub (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m + 1] : SSet.{u}).Subcomplex :=
  horn (m + 1) k

/-- The boundary of `Δ[m + 1]`. -/
private noncomputable def bdSub (m : ℕ) :
    (Δ[m + 1] : SSet.{u}).Subcomplex :=
  boundary (m + 1)

/-- Identification of `Δ[m]` with the `k`-th face. -/
private noncomputable def faceIso (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ≅ (faceSub m k : SSet.{u}) :=
  stdSimplex.faceSingletonComplIso k

/-- Lift a simplex of the `k`-th face back to `Δ[m]`. -/
private noncomputable def liftFace (m : ℕ) (k : Fin (m + 2)) {d : ℕ}
    (x : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (hxF : x ∈ (faceSub m k).obj _) : (Δ[m] : SSet.{u}) _⦋d⦌ :=
  (faceIso m k).inv.app _ ⟨x, hxF⟩

/-- The lift projects back down via `δ k`. -/
private lemma liftFace_spec (m : ℕ) (k : Fin (m + 2)) {d : ℕ}
    (x : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (hxF : x ∈ (faceSub m k).obj _) :
    x = (stdSimplex.δ k).app _ (liftFace m k x hxF) := by
  have h2 : (faceIso m k).hom.app _ (liftFace m k x hxF) = ⟨x, hxF⟩ := by
    have h : ((((faceIso m k).inv ≫ (faceIso m k).hom).app _ ⟨x, hxF⟩)) =
        ⟨x, hxF⟩ := by
      rw [(faceIso m k).inv_hom_id]
      rfl
    simp only [liftFace]
    exact h
  have h4 : (faceSub m k).ι.app _ (⟨x, hxF⟩ : (faceSub m k : SSet.{u}) _⦋d⦌) =
      x := rfl
  have h3 : ((stdSimplex.faceSingletonComplIso k).hom ≫
      (stdSimplex.face {k}ᶜ).ι).app _ (liftFace m k x hxF) = x := by
    change (faceSub m k).ι.app _ ((faceIso m k).hom.app _ (liftFace m k x hxF)) = x
    rw [h2, h4]
  rw [stdSimplex.faceSingletonComplIso_hom_ι] at h3
  exact h3.symm

/-- Ridge lemma: a simplex in both the horn and the `k`-th face lies over
`∂Δ[m]` under `e.inv`. If `x = δ k y` misses some `j ≠ k`, then `j` is
`sucAbove k j'` for a vertex `j'` missed by `y`. -/
private lemma face_data (m : ℕ) (k : Fin (m + 2)) {d : ℕ}
    (x : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (hxH : x ∈ (hornSub m k).obj _) (hxF : x ∈ (faceSub m k).obj _) :
    x = (stdSimplex.δ k).app _ (liftFace m k x hxF) ∧
      (liftFace m k x hxF) ∈ (boundary m).obj _ := by
  refine ⟨liftFace_spec m k x hxF, ?_⟩
  obtain ⟨j, hj_ne, hj⟩ := (mem_horn_iff_notMem_range x k).mp hxH
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hj_ne
  refine (mem_boundary_iff_notMem_range _).mpr ⟨j', ?_⟩
  rintro ⟨a, ha⟩
  apply hj
  refine ⟨a, ?_⟩
  have hxy := liftFace_spec m k x hxF
  have hcongr := congrArg (fun y : (Δ[m + 1] : SSet.{u}) _⦋d⦌ => y a) hxy
  have hδ : ((stdSimplex.δ k).app _ (liftFace m k x hxF)) a =
      k.succAbove ((liftFace m k x hxF) a) := rfl
  have hxa : x a = k.succAbove ((liftFace m k x hxF) a) := hcongr.trans hδ
  rw [hxa, ha, hj']

/-- The boundary is the union of the horn and the distinguished face. -/
private lemma sup_horn_face (m : ℕ) (k : Fin (m + 2)) :
    hornSub m k ⊔ faceSub m k = bdSub m := by
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨?_, face_singleton_compl_le_boundary k⟩
    change horn (m + 1) k ≤ boundary (m + 1)
    rw [horn_eq_iSup]
    exact iSup_le (fun j => face_singleton_compl_le_boundary j.1)
  · change boundary (m + 1) ≤ hornSub m k ⊔ faceSub m k
    rw [boundary_eq_iSup]
    apply iSup_le
    intro i
    by_cases hi : i = k
    · subst hi
      exact le_sup_right
    · exact (face_le_horn i k hi).trans le_sup_left

/-- Horn and face form a bicartesian square over the boundary. -/
private theorem bicart (m : ℕ) (k : Fin (m + 2)) :
    Subcomplex.BicartSq (hornSub m k ⊓ faceSub m k) (hornSub m k)
      (faceSub m k) (bdSub m) where
  sup_eq := sup_horn_face m k
  inf_eq := rfl

/-- The horn/face pushout over the boundary. -/
private theorem sqBase (m : ℕ) (k : Fin (m + 2)) : IsPushout
    (Subcomplex.homOfLE (bicart m k).le₁₂)
    (Subcomplex.homOfLE (bicart m k).le₁₃)
    (Subcomplex.homOfLE (bicart m k).le₂₄)
    (Subcomplex.homOfLE (bicart m k).le₃₄) :=
  (bicart m k).isPushout

/-- The tensored horn/face pushout (tensor with `Δ[1]` preserves colimits). -/
private theorem sqT (m : ℕ) (k : Fin (m + 2)) : IsPushout
    (Subcomplex.homOfLE (bicart m k).le₁₂ ▷ (Δ[1] : SSet.{u}))
    (Subcomplex.homOfLE (bicart m k).le₁₃ ▷ (Δ[1] : SSet.{u}))
    (Subcomplex.homOfLE (bicart m k).le₂₄ ▷ (Δ[1] : SSet.{u}))
    (Subcomplex.homOfLE (bicart m k).le₃₄ ▷ (Δ[1] : SSet.{u})) := by
  have : PreservesColimit (span (Subcomplex.homOfLE (bicart m k).le₁₂)
      (Subcomplex.homOfLE (bicart m k).le₁₃))
      (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) :=
    inferInstance
  exact (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})).map_isPushout
    (sqBase m k)

/-- Constant homotopy at `w` on the horn side. -/
private noncomputable def gHorn (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) :
    (hornSub m k : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  fst _ _ ≫ (hornSub m k).ι ≫ w

/-- Transported homotopy `H` on the distinguished-face side. -/
private noncomputable def gFace (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (faceSub m k : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  ((faceIso m k).inv ▷ (Δ[1] : SSet.{u})) ≫ H.h

/-- Agreement on the intersection: the constant side is `w`, while the
transported side is stationary at `δ k ≫ w` over `∂Δ[m]`. -/
private lemma agree_inf (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (Subcomplex.homOfLE (bicart m k).le₁₂ ▷ (Δ[1] : SSet.{u})) ≫ gHorn m k w =
      (Subcomplex.homOfLE (bicart m k).le₁₃ ▷ (Δ[1] : SSet.{u})) ≫
        gFace m k w v H := by
  ext n ⟨⟨x, hx⟩, t⟩
  have hxH : x ∈ (hornSub m k).obj n := hx.1
  have hxF : x ∈ (faceSub m k).obj n := hx.2
  obtain ⟨hxy, hy⟩ := face_data m k x hxH hxF
  have hstat := H.stationary (liftFace m k x hxF) hy t
  have hδy : (stdSimplex.δ k ≫ w).app n (liftFace m k x hxF) = w.app n x := by
    change w.app n ((stdSimplex.δ k).app n (liftFace m k x hxF)) = w.app n x
    rw [← hxy]
  change w.app n x = H.h.app n ⟨liftFace m k x hxF, t⟩
  rw [hstat]
  exact hδy.symm

/-- Glued map on the boundary cylinder. -/
private noncomputable def gBd (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (bdSub m : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (sqT m k).desc (gHorn m k w) (gFace m k w v H) (agree_inf m k w v H)

private lemma gBd_horn (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (Subcomplex.homOfLE (bicart m k).le₂₄ ▷ (Δ[1] : SSet.{u})) ≫
        gBd m k w v H = gHorn m k w :=
  (sqT m k).inl_desc (gHorn m k w) (gFace m k w v H) (agree_inf m k w v H)

private lemma gBd_face (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (Subcomplex.homOfLE (bicart m k).le₃₄ ▷ (Δ[1] : SSet.{u})) ≫
        gBd m k w v H = gFace m k w v H :=
  (sqT m k).inr_desc (gHorn m k w) (gFace m k w v H) (agree_inf m k w v H)

/-- The HEP prism `∂Δ[m+1] ⊗ Δ[1] ∪ Δ[m+1] ⊗ {0}`. -/
private noncomputable def prismR (m : ℕ) :
    (Δ[m + 1] ⊗ (Δ[1] : SSet.{u})).Subcomplex :=
  (bdSub m).unionProd (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)

/-- The vertex `{0} ↪ Δ[1]` inclusion is anodyne (it is the horn `Λ[1, 0]`). -/
private lemma face0_mem_anodyne :
    anodyneExtensions
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
      horn 1 (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
        = stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = horn 1 (0 : Fin 2) := by
          ext d x
          simp [horn_eq_iSup]
  rw [h_eq]
  exact anodyneExtensions.horn_ι (0 : Fin 2)

/-- The prism inclusion is anodyne, by the pushout-product theorem. -/
private lemma prismR_mem_anodyne (m : ℕ) :
    anodyneExtensions (prismR m).ι :=
  anodyneExtensions_unionProd_ι (bdSub m) _ face0_mem_anodyne

/-- Constant `w` on the initial end `Δ[m+1] ⊗ {0}`. -/
private noncomputable def gZero (m : ℕ)
    (w : Δ[m + 1] ⟶ F) : Δ[m + 1] ⊗
    ((stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ F :=
  fst _ _ ≫ w

/-- Agreement on `B ⊗ {0}`: both sides restrict to `w` on the boundary.
On the `gBd` side this splits by faces of `∂Δ[m+1]`; on the distinguished
face it uses that `{0}`-simplices are constant `0`, so `H.h` is read at its
initial endpoint `δ k ≫ w`. -/
private lemma agree_prism (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    ((bdSub m).ι ▷ ((stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) :
        SSet.{u})) ≫ gZero m w =
      (((bdSub m : SSet.{u}) ◁
          (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        gBd m k w v H) := by
  ext n ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have hL0 : (((bdSub m).ι ▷ _) ≫ gZero m w).app _ ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      = w.app _ s := rfl
  obtain ⟨i, hi⟩ : ∃ i : Fin (m + 2), s ∈ (stdSimplex.face {i}ᶜ).obj _ := by
    have hs'' : s ∈ (boundary (m + 1)).obj _ := hs
    rw [boundary_eq_iSup] at hs''
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hs''
    exact hs''
  by_cases hij : i = k
  · have hiF : s ∈ (faceSub m k).obj _ := hij ▸ hi
    have hR : ((((bdSub m : SSet.{u}) ◁
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        gBd m k w v H)).app _ ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ =
        (gFace m k w v H).app _ ⟨⟨s, hiF⟩, t⟩ := by
      have h3 := gBd_face m k w v H
      have h1 : ((((bdSub m : SSet.{u}) ◁ (stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex).ι) ≫ gBd m k w v H).app _
          ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) = (gBd m k w v H).app _ ⟨⟨s, hs⟩, t⟩ := rfl
      have h2 : ((((Subcomplex.homOfLE (bicart m k).le₃₄ ▷
          (Δ[1] : SSet.{u})) ≫ gBd m k w v H).app _ ⟨⟨s, hiF⟩, t⟩)) =
          (gBd m k w v H).app _ ⟨⟨s, hs⟩, t⟩ := rfl
      have hcongr := congrArg
        (fun f : ((faceSub m k : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F) =>
          f.app _ ⟨⟨s, hiF⟩, t⟩) h3
      rw [h2] at hcongr
      rw [h1]
      exact hcongr
    have ht0 : ∀ a, t a = (0 : Fin 2) := fun a =>
      Finset.mem_singleton.mp ((stdSimplex.mem_face_iff _ _).mp ht a)
    have hpair : (⟨liftFace m k s hiF, t⟩ :
        ((((Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj _))) =
        SSet.ι₀.app _ (liftFace m k s hiF) := by
      refine Prod.ext rfl ?_
      ext a
      have h01 : t a = (0 : Fin 2) := ht0 a
      have h02 : (SSet.ι₀.app _ (liftFace m k s hiF)).2 a = (0 : Fin 2) :=
        SSet.ι₀_app_snd_apply _ _
      rw [h01, h02]
    have hH0 : H.h.app _ ⟨liftFace m k s hiF, t⟩ =
        (stdSimplex.δ k ≫ w).app _ (liftFace m k s hiF) := by
      calc H.h.app _ ⟨liftFace m k s hiF, t⟩
          = H.h.app _ (SSet.ι₀.app _ (liftFace m k s hiF)) := by rw [← hpair]
        _ = (SSet.ι₀ ≫ H.h).app _ (liftFace m k s hiF) := rfl
        _ = (stdSimplex.δ k ≫ w).app _ (liftFace m k s hiF) := by rw [H.h₀]
    have hδy : (stdSimplex.δ k ≫ w).app _ (liftFace m k s hiF) = w.app _ s := by
      change w.app _ ((stdSimplex.δ k).app _ (liftFace m k s hiF)) = w.app _ s
      rw [← liftFace_spec m k s hiF]
    have hgF : (gFace m k w v H).app _ ⟨⟨s, hiF⟩, t⟩ = w.app _ s := by
      change H.h.app _ ⟨liftFace m k s hiF, t⟩ = w.app _ s
      rw [hH0, hδy]
    have hgoal : ((((bdSub m).ι ▷ ((stdSimplex.face {0} :
        (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gZero m w).app _
        ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) =
        ((((bdSub m : SSet.{u}) ◁ (stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex).ι) ≫ gBd m k w v H).app _
        ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) := by
      rw [hL0, hR, hgF]
    exact hgoal
  · have hiH : s ∈ (hornSub m k).obj _ := (face_le_horn i k hij) _ hi
    have hR : ((((bdSub m : SSet.{u}) ◁
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        gBd m k w v H)).app _ ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ =
        (gHorn m k w).app _ ⟨⟨s, hiH⟩, t⟩ := by
      have h3 := gBd_horn m k w v H
      have h1 : ((((bdSub m : SSet.{u}) ◁ (stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex).ι) ≫ gBd m k w v H).app _
          ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) = (gBd m k w v H).app _ ⟨⟨s, hs⟩, t⟩ := rfl
      have h2 : ((((Subcomplex.homOfLE (bicart m k).le₂₄ ▷
          (Δ[1] : SSet.{u})) ≫ gBd m k w v H).app _ ⟨⟨s, hiH⟩, t⟩)) =
          (gBd m k w v H).app _ ⟨⟨s, hs⟩, t⟩ := rfl
      have hcongr := congrArg
        (fun f : ((hornSub m k : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F) =>
          f.app _ ⟨⟨s, hiH⟩, t⟩) h3
      rw [h2] at hcongr
      rw [h1]
      exact hcongr
    have hgH : (gHorn m k w).app _ ⟨⟨s, hiH⟩, t⟩ = w.app _ s := rfl
    have hgoal : ((((bdSub m).ι ▷ ((stdSimplex.face {0} :
        (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gZero m w).app _
        ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) =
        ((((bdSub m : SSet.{u}) ◁ (stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex).ι) ≫ gBd m k w v H).app _
        ⟨⟨s, hs⟩, ⟨t, ht⟩⟩) := by
      rw [hL0, hR, hgH]
    exact hgoal

/-- Glued map on the prism. -/
private noncomputable def gR (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    (prismR m : SSet.{u}) ⟶ F :=
  (Subcomplex.unionProd.isPushout (bdSub m)
    (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (gZero m w) (gBd m k w v H) (agree_prism m k w v H)

private lemma gR_zero (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    Subcomplex.unionProd.ι₁ (bdSub m)
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) ≫ gR m k w v H =
      gZero m w :=
  (Subcomplex.unionProd.isPushout (bdSub m)
    (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inl_desc
    (gZero m w) (gBd m k w v H) (agree_prism m k w v H)

private lemma gR_bd (m : ℕ) (k : Fin (m + 2))
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    Subcomplex.unionProd.ι₂ (bdSub m)
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) ≫ gR m k w v H =
      gBd m k w v H :=
  (Subcomplex.unionProd.isPushout (bdSub m)
    (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inr_desc
    (gZero m w) (gBd m k w v H) (agree_prism m k w v H)

/-- Face correction along a rel-boundary homotopy, via Kan homotopy extension.

Assume `[KanComplex F]`. Given `H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)`,
a homotopy from the `k`-th face of `w` to `v`, stationary on `∂Δ[m]`, this produces
`w'` whose `k`-th face is exactly `v` (`δ k ≫ w' = v`) while every other face
`j ≠ k` is fixed (`δ j ≫ w' = δ j ≫ w`). See the module documentation. -/
theorem KanComplex.exists_correct_face_of_HomotopyRel [KanComplex F]
    (w : Δ[m + 1] ⟶ F) (v : Δ[m] ⟶ F)
    (H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)) :
    ∃ w' : Δ[m + 1] ⟶ F,
      stdSimplex.δ k ≫ w' = v ∧
      ∀ (j : Fin (m + 2)), j ≠ k →
        stdSimplex.δ j ≫ w' = stdSimplex.δ j ≫ w := by
  obtain ⟨Φ, hΦ⟩ := anodyneExtensions.exists_lift_of_isFibrant (gR m k w v H)
    (prismR_mem_anodyne m)
  have hΦ' : ((bdSub m).unionProd
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫ Φ =
      gR m k w v H := hΦ
  have hΦBd : ((bdSub m).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ = gBd m k w v H := by
    have h2 : (Subcomplex.unionProd.ι₂ (bdSub m)
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) ≫
        ((bdSub m).unionProd
          (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι) ≫ Φ
        = gBd m k w v H := by
      rw [Category.assoc, hΦ']
      exact (Subcomplex.unionProd.isPushout (bdSub m)
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inr_desc
        (gZero m w) (gBd m k w v H) (agree_prism m k w v H)
    rwa [Subcomplex.unionProd.ι₂_ι] at h2
  refine ⟨SSet.ι₁ ≫ Φ, ?_, ?_⟩
  · have hδk : stdSimplex.δ k = (faceIso m k).hom ≫ (faceSub m k).ι := by
      change stdSimplex.δ k = ((stdSimplex.faceSingletonComplIso k).hom ≫
        (stdSimplex.face {k}ᶜ).ι)
      rw [stdSimplex.faceSingletonComplIso_hom_ι]
    have e1 : (faceSub m k).ι ≫ SSet.ι₁
        = SSet.ι₁ ≫ ((faceSub m k).ι ▷ (Δ[1] : SSet.{u})) := by
      rw [SSet.ι₁_comp]
    have e3 : (faceIso m k).hom ≫ SSet.ι₁
        = SSet.ι₁ ≫ ((faceIso m k).hom ▷ (Δ[1] : SSet.{u})) := by
      rw [SSet.ι₁_comp]
    have e4 : ((faceIso m k).hom ▷ (Δ[1] : SSet.{u})) ≫ gFace m k w v H =
        H.h := by
      change ((faceIso m k).hom ▷ (Δ[1] : SSet.{u})) ≫
        (((faceIso m k).inv ▷ (Δ[1] : SSet.{u})) ≫ H.h) = H.h
      rw [← Category.assoc, hom_inv_whiskerRight, Category.id_comp]
    have hFaceRestrict : ((faceSub m k).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ =
        gFace m k w v H := by
      have hLe : (faceSub m k).ι =
          Subcomplex.homOfLE (bicart m k).le₃₄ ≫ (bdSub m).ι :=
        (Subcomplex.homOfLE_ι _).symm
      have h1 : ((faceSub m k).ι ▷ (Δ[1] : SSet.{u})) =
          (Subcomplex.homOfLE (bicart m k).le₃₄ ▷ (Δ[1] : SSet.{u})) ≫
            ((bdSub m).ι ▷ (Δ[1] : SSet.{u})) := by
        rw [hLe, comp_whiskerRight]
      rw [h1, Category.assoc, hΦBd]
      exact gBd_face m k w v H
    have bridge1 : (faceSub m k).ι ≫ (SSet.ι₁ ≫ Φ)
        = SSet.ι₁ ≫ (((faceSub m k).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ) := by
      conv_lhs => rw [← Category.assoc]
      rw [e1, Category.assoc]
    have bridge3 : (faceIso m k).hom ≫ (SSet.ι₁ ≫ gFace m k w v H)
        = SSet.ι₁ ≫ (((faceIso m k).hom ▷ (Δ[1] : SSet.{u})) ≫
          gFace m k w v H) := by
      conv_lhs => rw [← Category.assoc]
      rw [e3, Category.assoc]
    calc stdSimplex.δ k ≫ (SSet.ι₁ ≫ Φ)
        = (faceIso m k).hom ≫ ((faceSub m k).ι ≫ (SSet.ι₁ ≫ Φ)) := by
          rw [hδk, Category.assoc]
      _ = (faceIso m k).hom ≫
          (SSet.ι₁ ≫ (((faceSub m k).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ)) := by
          rw [bridge1]
      _ = (faceIso m k).hom ≫ (SSet.ι₁ ≫ gFace m k w v H) := by
          rw [hFaceRestrict]
      _ = SSet.ι₁ ≫ (((faceIso m k).hom ▷ (Δ[1] : SSet.{u})) ≫
          gFace m k w v H) := by rw [bridge3]
      _ = SSet.ι₁ ≫ H.h := by rw [e4]
      _ = v := H.h₁
  · intro j hj
    have hδj : SSet.horn.ι k j hj ≫ (hornSub m k).ι = stdSimplex.δ j :=
      SSet.horn.ι_ι _ _ _
    have f1 : (hornSub m k).ι ≫ SSet.ι₁
        = SSet.ι₁ ≫ ((hornSub m k).ι ▷ (Δ[1] : SSet.{u})) := by
      rw [SSet.ι₁_comp]
    have f2 : ((hornSub m k).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ = gHorn m k w := by
      have hLe : (hornSub m k).ι =
          Subcomplex.homOfLE (bicart m k).le₂₄ ≫ (bdSub m).ι :=
        (Subcomplex.homOfLE_ι _).symm
      have h1 : ((hornSub m k).ι ▷ (Δ[1] : SSet.{u})) =
          (Subcomplex.homOfLE (bicart m k).le₂₄ ▷ (Δ[1] : SSet.{u})) ≫
            ((bdSub m).ι ▷ (Δ[1] : SSet.{u})) := by
        rw [hLe, comp_whiskerRight]
      rw [h1, Category.assoc, hΦBd]
      exact gBd_horn m k w v H
    have hgHorn0 : SSet.ι₁ ≫ gHorn m k w = (hornSub m k).ι ≫ w := by
      change SSet.ι₁ ≫ (fst _ _ ≫ (hornSub m k).ι ≫ w) = (hornSub m k).ι ≫ w
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    have hHornW : (hornSub m k).ι ≫ (SSet.ι₁ ≫ Φ) = (hornSub m k).ι ≫ w := by
      calc (hornSub m k).ι ≫ (SSet.ι₁ ≫ Φ)
          = ((hornSub m k).ι ≫ SSet.ι₁) ≫ Φ := by rw [← Category.assoc]
        _ = (SSet.ι₁ ≫ ((hornSub m k).ι ▷ (Δ[1] : SSet.{u}))) ≫ Φ := by rw [f1]
        _ = SSet.ι₁ ≫ (((hornSub m k).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ) := by
            rw [Category.assoc]
        _ = SSet.ι₁ ≫ gHorn m k w := by rw [f2]
        _ = (hornSub m k).ι ≫ w := hgHorn0
    calc stdSimplex.δ j ≫ (SSet.ι₁ ≫ Φ)
        = (SSet.horn.ι k j hj ≫ (hornSub m k).ι) ≫ (SSet.ι₁ ≫ Φ) := by rw [hδj]
      _ = SSet.horn.ι k j hj ≫ ((hornSub m k).ι ≫ (SSet.ι₁ ≫ Φ)) :=
        Category.assoc _ _ _
      _ = SSet.horn.ι k j hj ≫ ((hornSub m k).ι ≫ w) :=
        congrArg (fun X => SSet.horn.ι k j hj ≫ X) hHornW
      _ = stdSimplex.δ j ≫ w := by
          have h : SSet.horn.ι k j hj ≫ ((hornSub m k).ι ≫ w) =
              (SSet.horn.ι k j hj ≫ (hornSub m k).ι) ≫ w :=
            (Category.assoc _ _ _).symm
          rw [h, hδj]

end SSet
