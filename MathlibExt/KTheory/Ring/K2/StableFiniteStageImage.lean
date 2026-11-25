/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteSupport
public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary

/-!
# Images of finite Steinberg stages

Identifies the image of a finite Steinberg stage with the corresponding
stabilized finite elementary subgroup. Its full preimage is the join of the
finite stage and the kernel of the map to the stable elementary group.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

variable {R : Type*} [Ring R]

@[expose] public section

theorem finiteStage_map_toStableE_eq_fromFinite_range (n : ℕ) :
    (finiteStage (R := R) n).map (toStableE (R := R)) =
      (StableE.fromFinite R n).range := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, finiteStage, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, j, hij, a, rfl, hi, hj⟩ := hg
    have hijFin : (⟨i, hi⟩ : Fin n) ≠ (⟨j, hj⟩ : Fin n) := by
      intro h
      exact hij (congrArg Fin.val h)
    have h_to : toStableE (R := R) (x i j hij a) =
        StableE.natElementary (R := R) i j hij a :=
      toStableE_x i j hij a
    have h_nat : StableE.natElementary (R := R) i j hij a =
        StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hijFin a := by
      have h := StableE.natElementary_fin (R := R) (n := n)
        (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hijFin a
      calc StableE.natElementary (R := R) i j hij a
          = StableE.natElementary (R := R)
              (⟨i, hi⟩ : Fin n).val (⟨j, hj⟩ : Fin n).val
              (fun h => hijFin (Fin.eq_of_val_eq h)) a := rfl
        _ = StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hijFin a := h
    have h_elem : StableE.fromFinite R n
        (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          ⟨i, hi⟩ ⟨j, hj⟩ hijFin a) =
        StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hijFin a :=
      StableE.fromFinite_elementary R _ _ _ _
    have h_eq : toStableE (R := R) (x (R := R) i j hij a) =
        StableE.fromFinite R n
          (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
            ⟨i, hi⟩ ⟨j, hj⟩ hijFin a) := by
      calc toStableE (R := R) (x (R := R) i j hij a)
          = StableE.natElementary (R := R) i j hij a := h_to
        _ = StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hijFin a := h_nat
        _ = StableE.fromFinite R n
            (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              ⟨i, hi⟩ ⟨j, hj⟩ hijFin a) := h_elem.symm
    have h_mem : StableE.fromFinite R n
        (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          ⟨i, hi⟩ ⟨j, hj⟩ hijFin a) ∈ (StableE.fromFinite R n).range :=
      MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h_mem' : toStableE (R := R) (x (R := R) i j hij a) ∈
        (StableE.fromFinite R n).range := h_eq ▸ h_mem
    exact (Subgroup.mem_comap).mpr h_mem'
  · intro y hy
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
    rw [← hg]
    have h_mem : (g : Matrix.GeneralLinearGroup (Fin n) R) ∈
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R := g.prop
    have key : ∀ (b : Matrix.GeneralLinearGroup (Fin n) R)
        (hb : b ∈ Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R),
        StableE.fromFinite R n ⟨b, hb⟩ ∈
          (finiteStage (R := R) n).map (toStableE (R := R)) := by
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨i, j, hij, a, rfl⟩ := hz
        have hi : i.val < n := i.isLt
        have hj : j.val < n := j.isLt
        have hijNat : i.val ≠ j.val := fun h => hij (Fin.eq_of_val_eq h)
        have h_nat : StableE.natElementary (R := R) i.val j.val hijNat a =
            StableE.elementary n i j hij a :=
          StableE.natElementary_fin n i j hij a
        have h_from : StableE.fromFinite R n
            (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary i j hij a) =
            StableE.elementary n i j hij a :=
          StableE.fromFinite_elementary R i j hij a
        have h_mem_fin : x (R := R) i.val j.val hijNat a ∈
            finiteStage (R := R) n :=
          x_mem_finiteStage hi hj
        have h_map_mem : toStableE (R := R) (x i.val j.val hijNat a) ∈
            (finiteStage (R := R) n).map (toStableE (R := R)) :=
          Subgroup.mem_map.mpr ⟨_, h_mem_fin, rfl⟩
        have h_to : toStableE (R := R) (x i.val j.val hijNat a) =
            StableE.natElementary (R := R) i.val j.val hijNat a :=
          toStableE_x _ _ _ _
        have h_eq : StableE.fromFinite R n
            ⟨Matrix.GeneralLinearGroup.elementary i j hij a,
              Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup i j hij a⟩ =
            toStableE (R := R) (x i.val j.val hijNat a) := by
          calc StableE.fromFinite R n
                ⟨Matrix.GeneralLinearGroup.elementary i j hij a,
                  Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup i j hij a⟩
              = StableE.elementary n i j hij a := h_from
            _ = StableE.natElementary (R := R) i.val j.val hijNat a := h_nat.symm
            _ = toStableE (R := R) (x i.val j.val hijNat a) := h_to.symm
        have h_eq2 : StableE.fromFinite R n
            ⟨Matrix.GeneralLinearGroup.elementary i j hij a,
              Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩⟩ =
            StableE.fromFinite R n
              ⟨Matrix.GeneralLinearGroup.elementary i j hij a,
                Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup i j hij a⟩ := rfl
        have : StableE.fromFinite R n
            ⟨Matrix.GeneralLinearGroup.elementary i j hij a,
              Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩⟩ ∈
            (finiteStage (R := R) n).map (toStableE (R := R)) := by
          rw [h_eq2, h_eq]
          exact h_map_mem
        exact this
      | one =>
        have h_eq : (⟨1, Subgroup.one_mem
            (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R)⟩ :
            Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) = 1 := rfl
        have h_one : StableE.fromFinite R n 1 = 1 := map_one _
        have : StableE.fromFinite R n
            ⟨1, Subgroup.one_mem
              (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R)⟩ ∈
            (finiteStage (R := R) n).map (toStableE (R := R)) := by
          rw [h_eq, h_one]
          exact Subgroup.one_mem _
        exact this
      | mul x y hx hy ihx ihy =>
        have h_eq : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ :
            Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) =
            ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        have h_mul : StableE.fromFinite R n ⟨x * y, Subgroup.mul_mem _ hx hy⟩ =
            StableE.fromFinite R n ⟨x, hx⟩ *
              StableE.fromFinite R n ⟨y, hy⟩ := by
          calc StableE.fromFinite R n ⟨x * y, Subgroup.mul_mem _ hx hy⟩
              = StableE.fromFinite R n (⟨x, hx⟩ * ⟨y, hy⟩) := by rw [h_eq]
            _ = StableE.fromFinite R n ⟨x, hx⟩ *
                StableE.fromFinite R n ⟨y, hy⟩ := by simp [map_mul]
        rw [h_mul]
        exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ihx =>
        have h_eq : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ :
            Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) =
            (⟨x, hx⟩ : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R)⁻¹ :=
          rfl
        have h_inv : StableE.fromFinite R n ⟨x⁻¹, Subgroup.inv_mem _ hx⟩ =
            (StableE.fromFinite R n ⟨x, hx⟩)⁻¹ := by
          calc StableE.fromFinite R n ⟨x⁻¹, Subgroup.inv_mem _ hx⟩
              = StableE.fromFinite R n
                  (⟨x, hx⟩ : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R)⁻¹ := by
                rw [h_eq]
            _ = (StableE.fromFinite R n ⟨x, hx⟩)⁻¹ := by simp
        rw [h_inv]
        exact Subgroup.inv_mem _ ihx
    exact key g.val g.prop

/-- The preimage of the finite-stage range in `StableE` under `toStableE`
is the finite stage joined with the kernel. The sup with `ker` corrects the
lack of injectivity; this does not claim `toStableE` is injective. -/
theorem comap_fromFinite_range_eq_finiteStage_sup_ker (n : ℕ) :
    Subgroup.comap (toStableE (R := R)) ((StableE.fromFinite R n).range) =
      finiteStage (R := R) n ⊔ (toStableE (R := R)).ker := by
  rw [← finiteStage_map_toStableE_eq_fromFinite_range (R := R) (n := n)]
  exact Subgroup.comap_map_eq (toStableE (R := R)) (finiteStage (R := R) n)

/-- If `g` in `finiteStage (n+1)` maps into the range of `fromFinite n`,
then `g` lies in `finiteStage n ⊔ ker toStableE`. -/
public theorem finiteStage_succ_mem_finiteStage_sup_ker_of_toStableE_mem_range
    {n : ℕ} {g : StableSteinberg R}
    (_hg : g ∈ finiteStage (R := R) (n + 1))
    (h_range : toStableE (R := R) g ∈ (StableE.fromFinite R n).range) :
    g ∈ finiteStage (R := R) n ⊔ (toStableE (R := R)).ker := by
  have h_mem_comap : g ∈
      Subgroup.comap (toStableE (R := R)) ((StableE.fromFinite R n).range) :=
    (Subgroup.mem_comap).mpr h_range
  have h_eq :
      Subgroup.comap (toStableE (R := R)) ((StableE.fromFinite R n).range) =
        finiteStage (R := R) n ⊔ (toStableE (R := R)).ker :=
    comap_fromFinite_range_eq_finiteStage_sup_ker (R := R) n
  rw [h_eq] at h_mem_comap
  exact h_mem_comap

/-- Every `Uₙ(R)` element has a `finiteStage n` preimage under
`toStableE` whose image is its `fromFinite` image. -/
public theorem exists_finiteStage_preimage_upperElementary
    (n : ℕ)
    (u : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) R) :
    ∃ g ∈ finiteStage (R := R) n,
      toStableE (R := R) g =
        StableE.fromFinite R n
          (Matrix.GeneralLinearGroup.UpperElementary.toElementarySubgroup
            u) := by
  have h_range :
      StableE.fromFinite R n
          (Matrix.GeneralLinearGroup.UpperElementary.toElementarySubgroup
            u) ∈
        (StableE.fromFinite R n).range :=
    MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have h_mem :
      StableE.fromFinite R n
          (Matrix.GeneralLinearGroup.UpperElementary.toElementarySubgroup
            u) ∈
        (finiteStage (R := R) n).map (toStableE (R := R)) := by
    rw [finiteStage_map_toStableE_eq_fromFinite_range (R := R) (n := n)]
    exact h_range
  obtain ⟨g, hg_mem, hg_eq⟩ := Subgroup.mem_map.mp h_mem
  exact ⟨g, hg_mem, hg_eq⟩

end
end StableSteinberg

end AlgebraicKTheory
