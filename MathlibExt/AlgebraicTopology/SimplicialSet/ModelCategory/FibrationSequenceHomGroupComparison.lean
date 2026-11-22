/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence

/-!
# Actual full homotopy-group maps of original fibration sequences

The original total, base, strict fibre and inclusion maps form the
complete natural diagram on every original pointed homotopy group.
All original point witnesses and full fibre maps are retained.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Simplicial
open scoped Simplicial

namespace SSet.FibrationSequenceHom

/-- The original fibre inclusion carries its original point to the chosen total point. -/
lemma fiberIncl_app_fiberPoint (S : FibrationSequence.{u}) :
    S.fiberIncl.app (Opposite.op ⦋0⦌) S.fiberPoint = S.e := rfl

variable {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T)

/-- Both original full total-to-base maps commute in every pointed degree. -/
theorem piMap_p_naturality (n : ℕ) (q : KanComplex.π n S.E S.e) :
    KanComplex.π.map T.p T.hb n (KanComplex.π.map f.totalMap f.total_pt n q) =
      KanComplex.π.map f.baseMap f.base_pt n (KanComplex.π.map S.p S.hb n q) :=
  (KanComplex.π.map_square f.totalMap f.baseMap S.p T.p f.comm.symm
    f.total_pt f.base_pt S.hb T.hb n q).symm

/-- The SAME entire fibre map and original total map commute with BOTH
full fibre inclusions in every original pointed degree. -/
theorem piMap_fiberIncl_naturality (n : ℕ) (q : KanComplex.π n S.fiber S.fiberPoint) :
    KanComplex.π.map T.fiberIncl (fiberIncl_app_fiberPoint T) n
        (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n q) =
      KanComplex.π.map f.totalMap f.total_pt n
        (KanComplex.π.map S.fiberIncl (fiberIncl_app_fiberPoint S) n q) :=
  (KanComplex.π.map_square f.fiberMap f.totalMap S.fiberIncl T.fiberIncl
    f.fiberMap_ι.symm f.fiberMap_app_basePoint f.total_pt
    (fiberIncl_app_fiberPoint S) (fiberIncl_app_fiberPoint T) n q).symm

/-- Original exactness detects the distinguished total class from the actual
base and fibre maps in every degree, including the genuine pointed π0 set. -/
theorem piMap_total_eq_one_of_map_eq_one (n : ℕ)
    (hBi : Function.Injective (KanComplex.π.map f.baseMap f.base_pt n))
    (hBs : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hFi : Function.Injective (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n))
    (q : KanComplex.π n S.E S.e)
    (hq : KanComplex.π.map f.totalMap f.total_pt n q = 1) : q = 1 := by
  have hb : KanComplex.π.map S.p S.hb n q = 1 := by
    apply hBi
    calc
      KanComplex.π.map f.baseMap f.base_pt n (KanComplex.π.map S.p S.hb n q) =
          KanComplex.π.map T.p T.hb n (KanComplex.π.map f.totalMap f.total_pt n q) :=
        (f.piMap_p_naturality n q).symm
      _ = 1 := by rw [hq, KanComplex.π.map_one]
      _ = KanComplex.π.map f.baseMap f.base_pt n 1 := (KanComplex.π.map_one _ _ _).symm
  obtain ⟨a, ha⟩ := S.exactness_at_E (n := n) q hb
  have hI : KanComplex.π.map T.fiberIncl (fiberIncl_app_fiberPoint T) n
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n a) = 1 :=
    (f.piMap_fiberIncl_naturality n a).trans
      ((congrArg (fun t => KanComplex.π.map f.totalMap f.total_pt n t) ha).trans hq)
  obtain ⟨b, hb⟩ := T.exactness_at_fiber (n := n) _ hI
  obtain ⟨c, hc⟩ := hBs b
  have hA : S.connectingMap (n := n) c = a := by
    apply hFi
    exact (FibrationSequence.connectingMap_naturality f c).trans
      ((congrArg (fun t => T.connectingMap (n := n) t) hc).trans hb)
  exact ha.symm.trans
    ((congrArg (fun t => KanComplex.π.map S.fiberIncl (fiberIncl_app_fiberPoint S) n t) hA.symm).trans
      (S.fiberIncl_map_connectingMap_eq_one c))

/-- Original exactness and the actual base/fibre comparison maps give
injectivity of the SAME total homotopy-group map in every positive degree. -/
theorem piMap_total_injective_succ (n : ℕ)
    (hBi : Function.Injective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hBs : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 2)))
    (hFi : Function.Injective (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint (n + 1))) :
    Function.Injective (KanComplex.π.map f.totalMap f.total_pt (n + 1)) := by
  let m := KanComplex.π.mapHom f.totalMap f.total_pt n
  intro a b hab
  have h : m (a / b) = 1 := by
    rw [map_div]
    change KanComplex.π.map f.totalMap f.total_pt (n + 1) a /
      KanComplex.π.map f.totalMap f.total_pt (n + 1) b = 1
    rw [hab, div_self']
    rfl
  exact div_eq_one.mp (f.piMap_total_eq_one_of_map_eq_one (n + 1) hBi hBs hFi _ h)

/-- The SAME actual original total map is surjective in positive degree.
Its preceding fibre term may be the genuine pointed π0 set. -/
theorem piMap_total_surjective_succ (n : ℕ)
    (hBs : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hFi : Function.Injective (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n))
    (hFs : Function.Surjective (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint (n + 1))) :
    Function.Surjective (KanComplex.π.map f.totalMap f.total_pt (n + 1)) := by
  let m := KanComplex.π.mapHom f.totalMap f.total_pt n
  let pT := KanComplex.π.mapHom T.p T.hb n
  intro q
  obtain ⟨b, hb⟩ := hBs (pT q)
  have hδ : S.connectingMap (n := n) b = 1 := by
    apply hFi
    calc
      KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n (S.connectingMap (n := n) b) =
          T.connectingMap (n := n) (KanComplex.π.map f.baseMap f.base_pt (n + 1) b) :=
        FibrationSequence.connectingMap_naturality f b
      _ = T.connectingMap (n := n) (pT q) := congrArg (fun t => T.connectingMap (n := n) t) hb
      _ = 1 := T.connectingMap_map_eq_one q
      _ = KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n 1 := (KanComplex.π.map_one _ _ _).symm
  obtain ⟨c, hc⟩ := S.exactness_at_B (n := n) b hδ
  have hp : pT (m c) = pT q :=
    (f.piMap_p_naturality (n + 1) c).trans
      ((congrArg (fun t => KanComplex.π.map f.baseMap f.base_pt (n + 1) t) hc).trans hb)
  have hr : pT (q / m c) = 1 := by
    rw [map_div, hp, div_self']
    rfl
  obtain ⟨a, ha⟩ := T.exactness_at_E (n := n + 1) (q / m c) hr
  obtain ⟨d, hd⟩ := hFs a
  refine ⟨KanComplex.π.map (x := S.fiberPoint) (y := S.e) S.fiberIncl (fiberIncl_app_fiberPoint S) (n + 1) d * c, ?_⟩
  change m (KanComplex.π.map (x := S.fiberPoint) (y := S.e) S.fiberIncl (fiberIncl_app_fiberPoint S) (n + 1) d * c) = q
  rw [map_mul]
  change KanComplex.π.map f.totalMap f.total_pt (n + 1)
      (KanComplex.π.map (x := S.fiberPoint) (y := S.e) S.fiberIncl (fiberIncl_app_fiberPoint S) (n + 1) d) * m c = q
  rw [← f.piMap_fiberIncl_naturality, hd, ha]
  exact div_mul_cancel _ _

/-- Full original base and fibre homotopy-group bijectivity detects each
SAME complete original positive-degree total map. -/
theorem piMap_total_bijective_succ (n : ℕ)
    (hB : ∀ k, Function.Bijective (KanComplex.π.map f.baseMap f.base_pt k))
    (hF : ∀ k, Function.Bijective (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint k)) :
    Function.Bijective (KanComplex.π.map f.totalMap f.total_pt (n + 1)) :=
  ⟨f.piMap_total_injective_succ n (hB (n + 1)).1 (hB (n + 2)).2 (hF (n + 1)).1,
    f.piMap_total_surjective_succ n (hB (n + 1)).2 (hF n).1 (hF (n + 1)).2⟩

end SSet.FibrationSequenceHom
