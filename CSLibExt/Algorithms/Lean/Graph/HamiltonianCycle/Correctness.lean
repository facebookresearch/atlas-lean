/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Characteristic
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Walk
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Encoding

/-!+# Hamiltonian-cycle verifier correctness

CLRS4 requires an ordered certificate containing every vertex once and checks
each consecutive edge, including the closing edge. This implementation chooses
a square row-major graph encoding with diagonal and symmetry validation and
exact-length fixed-width binary vertex words. The characteristic below observes
that actual short-circuit saved-state executor, including rejects.
-/

namespace Cslib.Algorithms.Lean.Graph

/-- The actual verifier accepts exactly its graph encoding and ordered-cycle checks. -/
public theorem verifyHamiltonianCycle_iff (x y : Array Bool) :
    let m := Nat.sqrt x.size
    let w := Nat.clog 2 m
    let decode := fun i : Nat => Nat.ofDigits 2
      ((y.toList.drop (i * w)).take w |>.map fun bit => if bit then 1 else 0)
    (verifyHamiltonianCycle x y).ret = true ↔
      m * m = x.size ∧ 3 ≤ m ∧ y.size = m * w ∧
      (∀ i < m, x[i * m + i]? = some false) ∧
      (∀ i < m, ∀ j < m, x[i * m + j]? = x[j * m + i]?) ∧
      (∀ i < m, decode i < m) ∧
      (∀ i < m, ∀ j < m, decode i = decode j → i = j) ∧
      (∀ i < m, x[decode i * m + decode ((i + 1) % m)]? = some true) := by
  dsimp only
  let d : Nat → Nat := fun i => Nat.ofDigits 2
    ((y.toList.drop (i * Nat.clog 2 (Nat.sqrt x.size))).take
      (Nat.clog 2 (Nat.sqrt x.size)) |>.map fun bit => if bit then 1 else 0)
  have h := verify_order_iff x y
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨hv, hm, hy, f, hd, hf, he⟩
    obtain ⟨hs, hdiag, hsymm⟩ := (validateGraph_nat_iff _ _).mp hv
    obtain ⟨hr, hi, he'⟩ := order_nat_forward x _ d f hd hf he
    exact ⟨hs, hm, hy, hdiag, hsymm, hr, hi,
      (order_optional_iff x _ d hs hr).mp he'⟩
  · rintro ⟨hs, hm, hy, hdiag, hsymm, hr, hi, he⟩
    have hv := (validateGraph_nat_iff x _).mpr ⟨hs, hdiag, hsymm⟩
    have he' := (order_optional_iff x _ d hs hr).mpr he
    exact ⟨hv, hm, hy, order_nat_backward x _ d hr hi he'⟩

/-- Every accepted certificate gives a canonical Hamiltonian cycle in the encoded graph. -/
public theorem verifyHamiltonianCycle_sound (x y : Array Bool)
    (h : (verifyHamiltonianCycle x y).ret = true) :
    let m := Nat.sqrt x.size
    m * m = x.size ∧ 3 ≤ m ∧
      ∃ G : SimpleGraph (Fin m),
        (∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true) ∧
        ∃ v : Fin m, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  dsimp only
  have ho := verify_order_iff x y
  dsimp only at ho
  obtain ⟨hv, hm, _, f, _, hf, he⟩ := ho.mp h
  obtain ⟨hs, hd, hsymm⟩ := (validateGraph_iff _ _).mp hv
  obtain ⟨G, hG⟩ := graph_of_validated_array x _ hd hsymm
  refine ⟨hs, hm, G, hG, hamiltonianCycle_of_order _ hm G f hf ?_⟩
  intro i
  apply (hG _ _).mpr
  have hb : (f i).val * Nat.sqrt x.size +
      (f ⟨(i.val + 1) % Nat.sqrt x.size, Nat.mod_lt _ (by omega)⟩).val < x.size := by
    exact lt_of_lt_of_eq (row_major_lt _ _ _ (f i).isLt (f _).isLt) hs
  have hr := graph_read_some x _ hb
  rwa [he i] at hr

/-- Every canonical Hamiltonian cycle has an accepted exact fixed-width certificate. -/
public theorem verifyHamiltonianCycle_complete (x : Array Bool) :
    let m := Nat.sqrt x.size
    ∀ G : SimpleGraph (Fin m), m * m = x.size →
      (∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true) →
      ∀ (v : Fin m) (p : G.Walk v v), p.IsHamiltonianCycle →
        ∃ y : Array Bool, y.size = m * Nat.clog 2 m ∧
          (verifyHamiltonianCycle x y).ret = true := by
  dsimp only
  intro G hs hG v p hp
  have hm : 3 ≤ Nat.sqrt x.size := by
    simpa only [hp.length_eq, Fintype.card_fin] using hp.three_le_length
  obtain ⟨f, hf, he⟩ := order_of_hamiltonianCycle _ G v p hp
  obtain ⟨y, hy, hd⟩ := encode_order _ (Nat.clog 2 (Nat.sqrt x.size)) f
    (Nat.le_pow_clog (by decide) _)
  refine ⟨y, hy, ?_⟩
  have ho := verify_order_iff x y
  dsimp only at ho
  apply ho.mpr
  refine ⟨validated_array_of_graph x _ G hs hG, hm, hy, f, hd, hf, ?_⟩
  intro i
  rw [(hG _ _).mp (he i)]
  rfl

/-- Certificate existence is exactly strict canonical Hamiltonian-cycle existence. -/
public theorem verifyHamiltonianCycle_language_iff (x : Array Bool) :
    (∃ y : Array Bool, (verifyHamiltonianCycle x y).ret = true) ↔
      let m := Nat.sqrt x.size
      m * m = x.size ∧ 3 ≤ m ∧
        ∃ G : SimpleGraph (Fin m),
          (∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true) ∧
          ∃ v : Fin m, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  constructor
  · rintro ⟨y, hy⟩
    exact verifyHamiltonianCycle_sound x y hy
  · rintro ⟨hs, _, G, hG, v, p, hp⟩
    obtain ⟨y, _, hy⟩ := verifyHamiltonianCycle_complete x G hs hG v p hp
    exact ⟨y, hy⟩

end Cslib.Algorithms.Lean.Graph
