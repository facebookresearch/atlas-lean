/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateScalarMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateEndpointCore
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCartesianPairingWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellMarkingCoverage

/-!
# Genuine weak original root-coordinate scalar attachments

The actual opposite endpoint/scalar-boundary core retains its original
rank and every original simplex map. Every final horn's original final
edge lies over the unchanged final scalar vertex, so its actual original
maximum is unchanged and that edge is marked in the old stage. The same
controlled native rank ladder proves the original marked scalar cell a
trivial cofibration in the genuine coefficient model.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

local instance rootCoordinateScalarCoreRegular (d : ℕ) : (rootCoordinateEndpointCore.{u} d).IsRegular := by
  dsimp only [rootCoordinateEndpointCore]
  infer_instance

local instance rootCoordinateScalarPairingRegular (d : ℕ) : (rootCoordinateEndpointCore.{u} d).pairing.IsRegular :=
  (Subcomplex.PairingCore.isRegular_pairing_iff _).mpr inferInstance

/-- The same actual native final-index coordinate core edge is originally marked by its unchanged original final
scalar maximum. -/
theorem coneRootCoordinateScalarCore_final_edge_marked {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n))
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d) (hs : s.index = 0) :
    (yonedaEquiv.symm ((rootCoordinateEndpointCore d).simplex s)).app (op ⦋1⦌)
        (stdSimplex.edge (s.d + 1) (Fin.last s.d).castSucc (Fin.last (s.d + 1)) (Fin.le_last _)) ∈
      (coneRootCoordinateScalarAmbient j hj a).marking := by
  have hgrid := rootCoordinateEndpointCore_final_grid d s hs
  apply coneRootCoordinateScalarAmbient_final_edge_marked j hj hj' a ha
  · change ((rootCoordinateEndpointCore d).simplex s).2 (Fin.last s.d).castSucc = Fin.last d
    exact congrArg Prod.snd hgrid.1
  · change ((rootCoordinateEndpointCore d).simplex s).2 (Fin.last (s.d + 1)) = Fin.last d
    exact congrArg Prod.snd hgrid.2

private theorem scalarFinalCell_last_edge_marked {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n))
    (r : ℕ) (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) d)
    (ht : (rootCoordinateEndpointCore.{u} d).pairing.rankFunction.rank
      ((rootCoordinateEndpointCore.{u} d).equivII s) = r)
    (hz : (⟨(rootCoordinateEndpointCore.{u} d).equivII s, ht⟩ :
      (rootCoordinateEndpointCore.{u} d).pairing.rankFunction.Cell r).index = Fin.last (s.d + 1)) :
    let c : (rootCoordinateEndpointCore.{u} d).pairing.rankFunction.Cell r :=
      ⟨(rootCoordinateEndpointCore.{u} d).equivII s, ht⟩
    c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _)) ∈
      (coneRootCoordinateScalarAmbient j hj a).marking := by
  let h := rootCoordinateEndpointCore.{u} d
  let f := h.pairing.rankFunction
  let c : f.Cell r := ⟨h.equivII s, ht⟩
  have hidx : c.index = s.index.castSucc.rev := h.rankCell_index f s ht
  have hs : s.index = 0 := by
    have hi : s.index.castSucc.rev = Fin.last (s.d + 1) := hidx.symm.trans hz
    have hh := congrArg Fin.rev hi
    simpa only [Fin.rev_rev, Fin.rev_last, Fin.castSucc_eq_zero_iff] using hh
  have hcmap : c.map = yonedaEquiv.symm (h.simplex s) := by
    have hmap := h.rankCell_map f s ht
    change c.map = 𝟙 _ ≫ yonedaEquiv.symm (h.simplex s) at hmap
    exact hmap.trans (Category.id_comp _)
  exact (congrArg (fun z : (Δ[s.d + 1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[d] =>
    z.app (op ⦋1⦌)
      (stdSimplex.edge (s.d + 1) (Fin.last s.d).castSucc (Fin.last (s.d + 1)) (Fin.le_last _)) ∈
        (coneRootCoordinateScalarAmbient j hj a).marking) hcmap).to_iff.mpr
    (coneRootCoordinateScalarCore_final_edge_marked j hj hj' a ha s hs)

private theorem scalarFinalCell_horn_edge_mem {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (r : ℕ) (c : (rootCoordinateEndpointCore.{u} d).pairing.rankFunction.Cell r)
    (e : c.horn.toSSet _⦋1⦌)
    (he : c.horn.ι.app (op ⦋1⦌) e =
      stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _))
    (hm : c.map.app (op ⦋1⦌)
      (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _)) ∈
      (coneRootCoordinateScalarAmbient j hj a).marking) :
    c.mapHorn.app (op ⦋1⦌) e ∈
      (comap (coneRootCoordinateScalarAmbient j hj a)
        ((rootCoordinateEndpointCore.{u} d).pairing.rankFunction.filtration r).ι).marking := by
  let f := (rootCoordinateEndpointCore.{u} d).pairing.rankFunction
  have hr : (f.filtration r).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) =
      c.map.app (op ⦋1⦌)
        (stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _)) :=
    (Subcomplex.Pairing.RankFunction.Cell.mapHorn_app_ι f c e).trans
      (congrArg (c.map.app (op ⦋1⦌)) he)
  change (f.filtration r).ι.app (op ⦋1⦌) (c.mapHorn.app (op ⦋1⦌) e) ∈
    (coneRootCoordinateScalarAmbient j hj a).marking
  exact hr.symm ▸ hm

private theorem scalarExists_final_critical (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 2))
    (hi : i = Fin.last (d + 1)) :
    ∃ e : (horn.{u} (d + 1) i : SSet.{u}) _⦋1⦌,
      (horn.{u} (d + 1) i).ι.app (op ⦋1⦌) e =
        stdSimplex.edge (d + 1) (Fin.last d).castSucc (Fin.last (d + 1)) (Fin.le_last _) := by
  subst i
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  exact ⟨rightHornEdgeSimplex.{u} m, rfl⟩

/-- The original rank pairing of the same original marked coordinate/scalar cell has only inner horns or actual
final horns with their original final edge marked at the old stage. -/
theorem coneRootCoordinateScalar_pairing_controlled {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n)) :
    @CartesianControlledPairing.{u} (coneRootCoordinateScalarAmbient j hj a)
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d))
      (rootCoordinateEndpointCore.{u} d).pairing (rootCoordinateScalarPairingRegular d) := by
  let ambient := coneRootCoordinateScalarAmbient j hj a
  let A := Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)
  let h := rootCoordinateEndpointCore.{u} d
  let f := h.pairing.rankFunction
  have hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌) :=
    coneRootCoordinateScalarAmbient_marks_mem j hj hj' hd a ha₀ ha₁
  intro r c
  rcases c with ⟨t, ht⟩
  obtain ⟨s, rfl⟩ := h.equivII.surjective t
  let c : f.Cell r := ⟨h.equivII s, ht⟩
  have hidx : c.index.val = s.index.castSucc.rev.val := h.rankCell_index_val f s ht
  have hpos : 0 < c.index := by
    change 0 < c.index.val
    simp only [Fin.val_rev, Fin.val_castSucc] at hidx
    have hs := s.index.isLt
    omega
  by_cases hz : c.index = Fin.last (c.dim + 1)
  · right
    have hd' : 1 ≤ c.dim :=
      Subcomplex.N.one_le_dim_of_vertices (vertices_mem_of_marks_mem ambient A hmarks) c.s.val
    obtain ⟨e, he⟩ := scalarExists_final_critical c.dim hd' c.index hz
    exact ⟨hd', hz, e, he, scalarFinalCell_horn_edge_mem j hj a r c e he
      (scalarFinalCell_last_edge_marked j hj hj' a ha₁ r s ht hz)⟩
  · left
    exact ⟨hpos, lt_of_le_of_ne (Fin.le_last _) hz⟩

/-- The same original coordinate/scalar endpoint-boundary inclusion keeps its exact original inherited marking and
underlying union. -/
def coneRootCoordinateScalarCell {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    comap (coneRootCoordinateScalarAmbient j hj a)
        (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ⟶
      coneRootCoordinateScalarAmbient j hj a :=
  comapHom (coneRootCoordinateScalarAmbient j hj a)
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι

/-- The actual whole original marked coordinate/scalar cell is a genuine coefficient trivial cofibration, through
its same original controlled rank ladder. -/
theorem coneRootCoordinateScalarCell_trivialCofibration {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n)) :
    trivialCofibrations Marked.{u} (coneRootCoordinateScalarCell j hj a) :=
  @coherentConeCartesianPairing_trivialCofibration.{u}
    (coneRootCoordinateScalarAmbient j hj a)
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d))
    (rootCoordinateEndpointCore.{u} d).pairing
    (rootCoordinateScalarPairingRegular d)
    (coneRootCoordinateScalarAmbient_marks_mem j hj hj' hd a ha₀ ha₁)
    (coneRootCoordinateScalar_pairing_controlled j hj hj' hd a ha₀ ha₁)

end SSet.Marked.CoherentWeight
