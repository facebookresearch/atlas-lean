/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.MultibondReindex
import Code.FrontierA.IsingSurfaceTensionSheetPositionReduction

open Finset

namespace StatMech.FrontierA

noncomputable section


def cubicalCellZReflect {a b c : Nat} (q : CubicalCell a b c) :
    CubicalCell a b c :=
  ⟨q.x, q.y, q.z.rev⟩

def cubicalCellZReflectEquiv (a b c : Nat) :
    CubicalCell a b c ≃ CubicalCell a b c where
  toFun := cubicalCellZReflect
  invFun := cubicalCellZReflect
  left_inv q := by cases q; simp [cubicalCellZReflect]
  right_inv q := by cases q; simp [cubicalCellZReflect]


def cubicalDualVertexZReflectEquiv (a b c : Nat) :
    CubicalDualVertex a b c ≃ CubicalDualVertex a b c :=
  Equiv.optionCongr (cubicalCellZReflectEquiv a b c)

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_none
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s none =
      s none := rfl

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_some
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (q : CubicalCell a b c) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (some (cubicalCellZReflect q)) = s (some q) := by
  change s (some (cubicalCellZReflect (cubicalCellZReflect q))) = s (some q)
  congr 2
  cases q
  simp [cubicalCellZReflect]

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_mk
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (x : Fin a) (y : Fin b) (z : Fin c) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (some (⟨x, y, z.rev⟩ : CubicalCell a b c)) =
      s (some ⟨x, y, z⟩) := by
  exact multibondConfigReindex_cubicalDualVertexZReflect_some s ⟨x, y, z⟩

theorem finBackward_rev_map_rev {n : Nat} (k : Fin (n + 1)) :
    (finBackward k.rev).map Fin.rev = finForward k := by
  apply Option.ext
  intro z
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    apply (finForward_eq_some_iff k z).2
    have hkr := (finBackward_eq_some_iff k.rev w).1 hw
    have hrev := congrArg Fin.rev hkr
    simpa [← hwz, Fin.rev_succ] using hrev
  · intro hz
    have hk := (finForward_eq_some_iff k z).1 hz
    refine ⟨z.rev, ?_, by simp⟩
    apply (finBackward_eq_some_iff k.rev z.rev).2
    rw [hk, Fin.rev_castSucc]

theorem finForward_rev_map_rev {n : Nat} (k : Fin (n + 1)) :
    (finForward k.rev).map Fin.rev = finBackward k := by
  apply Option.ext
  intro z
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    apply (finBackward_eq_some_iff k z).2
    have hkr := (finForward_eq_some_iff k.rev w).1 hw
    have hrev := congrArg Fin.rev hkr
    simpa [← hwz, Fin.rev_castSucc] using hrev
  · intro hz
    have hk := (finBackward_eq_some_iff k z).1 hz
    refine ⟨z.rev, ?_, by simp⟩
    apply (finForward_eq_some_iff k.rev z.rev).2
    rw [hk, Fin.rev_succ]

theorem multibondConfigReindex_cubicalDualVertexZReflect_optionMap
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (x : Fin a) (y : Fin b) (o : Option (Fin c)) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (o.map fun z => (⟨x, y, z⟩ : CubicalCell a b c)) =
      s (o.map fun z => (⟨x, y, z.rev⟩ : CubicalCell a b c)) := by
  cases o with
  | none => rfl
  | some z =>
      change multibondConfigReindex
          (cubicalDualVertexZReflectEquiv a b c) s (some ⟨x, y, z⟩) =
        s (some ⟨x, y, z.rev⟩)
      simpa using
        (multibondConfigReindex_cubicalDualVertexZReflect_mk s x y z.rev)


def cubicalPlaquetteZReflect {a b c : Nat} :
    CubicalPlaquette a b c -> CubicalPlaquette a b c
  | .xy i j k => .xy i j k.rev
  | .xz i j k => .xz i j k.rev
  | .yz i j k => .yz i j k.rev

def cubicalPlaquetteZReflectEquiv (a b c : Nat) :
    CubicalPlaquette a b c ≃ CubicalPlaquette a b c where
  toFun := cubicalPlaquetteZReflect
  invFun := cubicalPlaquetteZReflect
  left_inv p := by cases p <;> simp [cubicalPlaquetteZReflect]
  right_inv p := by cases p <;> simp [cubicalPlaquetteZReflect]

theorem cubicalPlaquetteZReflectEquiv_map_xySheet
    {a b c : Nat} (k : Fin (c + 1)) :
    (cubicalXYSheet (a := a) (b := b) k).map
        (cubicalPlaquetteZReflectEquiv a b c).toEmbedding =
      cubicalXYSheet (a := a) (b := b) k.rev := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [cubicalXYSheet, Finset.mem_image] at hq ⊢
    obtain ⟨ij, _, rfl⟩ := hq
    exact ⟨ij, Finset.mem_univ _, rfl⟩
  · intro hp
    simp only [cubicalXYSheet, Finset.mem_image] at hp
    obtain ⟨ij, _, rfl⟩ := hp
    rw [Finset.mem_map]
    refine ⟨CubicalPlaquette.xy ij.1 ij.2 k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
    · simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect]

theorem cubicalDualEnds_zReflect_agrees
    {a b c : Nat} (p : CubicalPlaquette a b c)
    (s : CubicalDualVertex a b c -> Bool) :
    (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s)
          (cubicalDualEnds
            ((cubicalPlaquetteZReflectEquiv a b c) p)).1 =
        (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s)
          (cubicalDualEnds
            ((cubicalPlaquetteZReflectEquiv a b c) p)).2 <->
      s (cubicalDualEnds p).1 = s (cubicalDualEnds p).2 := by
  cases p with
  | xy i j k =>
      change multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
            ((finBackward k.rev).map fun z =>
              (⟨i, j, z⟩ : CubicalCell a b c)) =
          multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
            ((finForward k.rev).map fun z =>
              (⟨i, j, z⟩ : CubicalCell a b c)) <->
        s ((finBackward k).map fun z =>
            (⟨i, j, z⟩ : CubicalCell a b c)) =
          s ((finForward k).map fun z =>
            (⟨i, j, z⟩ : CubicalCell a b c))
      rw [multibondConfigReindex_cubicalDualVertexZReflect_optionMap,
        multibondConfigReindex_cubicalDualVertexZReflect_optionMap]
      have hb : (finBackward k.rev).map (fun z =>
            (⟨i, j, z.rev⟩ : CubicalCell a b c)) =
          (finForward k).map (fun z => ⟨i, j, z⟩) := by
        change Option.map ((fun z => (⟨i, j, z⟩ : CubicalCell a b c)) ∘ Fin.rev)
            (finBackward k.rev) = _
        rw [← Option.map_map, finBackward_rev_map_rev]
      have hf : (finForward k.rev).map (fun z =>
            (⟨i, j, z.rev⟩ : CubicalCell a b c)) =
          (finBackward k).map (fun z => ⟨i, j, z⟩) := by
        change Option.map ((fun z => (⟨i, j, z⟩ : CubicalCell a b c)) ∘ Fin.rev)
            (finForward k.rev) = _
        rw [← Option.map_map, finForward_rev_map_rev]
      rw [hb, hf]
      exact eq_comm
  | xz i j k =>
      cases hb : finBackward j <;> cases hf : finForward j <;>
        simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect,
          cubicalDualEnds, hb, hf]
  | yz i j k =>
      cases hb : finBackward i <;> cases hf : finForward i <;>
        simp [cubicalPlaquetteZReflectEquiv, cubicalPlaquetteZReflect,
          cubicalDualEnds, hb, hf]



theorem multibondDisorderFreeEnergy_cubicalXYSheet_rev
    {a b c : Nat} (beta : Real) (k : Fin (c + 1)) :
    multibondDisorderFreeEnergy
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (fun _ : CubicalPlaquette a b c => beta)
        (cubicalXYSheet k.rev) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette a b c => beta) (cubicalXYSheet k) := by
  rw [← cubicalPlaquetteZReflectEquiv_map_xySheet k]
  apply multibondDisorderFreeEnergy_reindex
    (cubicalPlaquetteZReflectEquiv a b c)
    (cubicalDualVertexZReflectEquiv a b c)
  · intro p
    rfl
  · exact cubicalDualEnds_zReflect_agrees

end

end StatMech.FrontierA
