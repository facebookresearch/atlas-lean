/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting










namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictIncidenceDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

@[simp] theorem randomCurrent_sources_empty
    {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (ends : E -> Sym2 W) :
    RandomCurrent.sources ends ∅ = ∅ := by
  ext x
  simp [RandomCurrent.sources, RandomCurrent.degK]



theorem randomCurrent_connK_insert_edge_cases
    {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E]
    (ends : E -> Sym2 W) (K : Finset E) (d : E) {a b : W}
    (hconn : connK ends (insert d K) a b) :
    connK ends K a b ∨
      ∃ x ∈ ends d, ∃ y ∈ ends d,
        connK ends K a x ∧ connK ends K y b := by
  induction hconn with
  | refl =>
      exact Or.inl Relation.ReflTransGen.refl
  | @tail x y _ hstep ih =>
      obtain ⟨e, he, hx, hy, hxy⟩ := hstep
      rcases Finset.mem_insert.mp he with rfl | heK
      · rcases ih with hax | ⟨u, hu, v, hv, hau, hvx⟩
        · exact Or.inr ⟨x, hx, y, hy, hax,
            Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨u, hu, y, hy, hau,
            Relation.ReflTransGen.refl⟩
      · have hxyK : connK ends K x y :=
          Relation.ReflTransGen.single ⟨e, heK, hx, hy, hxy⟩
        rcases ih with hax | ⟨u, hu, v, hv, hau, hvx⟩
        · exact Or.inl (hax.trans hxyK)
        · exact Or.inr ⟨u, hu, v, hv, hau, hvx.trans hxyK⟩



theorem randomCurrent_connK_eq_or_common_edge_of_unique_incidence
    {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E]
    (ends : E -> Sym2 W) (K : Finset E) (B : Finset W)
    (hsupport : K.biUnion (fun e => (ends e).toFinset) = B)
    (hunique : ∀ x ∈ B,
      ∃! e, e ∈ K ∧ x ∈ (ends e).toFinset)
    {a b : W} (ha : a ∈ B) (hconn : connK ends K a b) :
    a = b ∨ ∃ e ∈ K, a ∈ ends e ∧ b ∈ ends e := by
  induction hconn with
  | refl => exact Or.inl rfl
  | @tail x y _ hstep ih =>
      obtain ⟨f, hfK, hxf, hyf, hxy⟩ := hstep
      have hxB : x ∈ B := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨f, hfK, Sym2.mem_toFinset.mpr hxf⟩
      rcases ih with rfl | ⟨e, heK, hae, hxe⟩
      · exact Or.inr ⟨f, hfK, hxf, hyf⟩
      · obtain ⟨_, _, huniqueX⟩ := hunique x hxB
        have hef : e = f := huniqueX e
          ⟨heK, Sym2.mem_toFinset.mpr hxe⟩ |>.trans
            (huniqueX f ⟨hfK, Sym2.mem_toFinset.mpr hxf⟩).symm
        subst f
        exact Or.inr ⟨e, heK, hae, hyf⟩



theorem lpReplica_threeSeam_toggle_two_eq_selected_third
    {W : Type*} [DecidableEq W]
    (S : I -> Finset W) (T : Finset W)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v) :
    let l := lpReplicaThirdOfThree i j k u v
    S i ∆ S j ∆ T ∆ (S u ∆ S v) = S k ∆ S l ∆ T := by
  dsimp only
  rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    simp_all [lpReplicaThirdOfThree, symmDiff_assoc,
      symmDiff_left_comm, symmDiff_comm] <;>
    split_ifs <;> simp_all [symmDiff_comm]



theorem sym2_toFinset_map_embedding
    {W X : Type*} [DecidableEq W] [DecidableEq X]
    (f : W → X) (hf : Function.Injective f) (e : Sym2 W) :
    (Sym2.map f e).toFinset = e.toFinset.map ⟨f, hf⟩ := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      ext z
      simp



theorem lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    {u v : I} (huv : u ≠ v)
    (hfold : lpReplicaCurrentFoldedEdge G sites e =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    (∃ x y : V, e.1 =
        s((.inl (.inl x) : LPReplicaCurrentVertex V), .inl (.inl y))) ∨
      (∃ x y : V, e.1 =
        s((.inl (.inr x) : LPReplicaCurrentVertex V), .inl (.inr y))) := by
  have hsuv : sites u ≠ sites v := hsite.ne huv
  induction hval : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (lpReplicaCurrentGraph G sites).Adj x y := by
        have hmem := e.2
        rw [SimpleGraph.mem_edgeFinset, hval, SimpleGraph.mem_edgeSet] at hmem
        exact hmem
      unfold lpReplicaCurrentFoldedEdge at hfold
      rw [hval, Sym2.map_mk] at hfold
      rcases x with (x | g) <;> rcases y with (y | h)
      · rcases x with x | x <;> rcases y with y | y
        · exact Or.inl ⟨x, y, rfl⟩
        · rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, htx, hty⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv
              (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv
              (h.2.symm.trans (hxy'.symm.trans h.1)))
        · rw [(lpReplicaCurrentGraph G sites).adj_comm,
              lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, hty, htx⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv
              (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv
              (h.2.symm.trans (hxy'.symm.trans h.1)))
        · exact Or.inr ⟨x, y, rfl⟩
      · rcases x with x | x <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> rcases y with y | y <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold




theorem lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (x : LPReplicaCurrentVertex V)
    (hx : x ∈ endsM (lpReplicaCurrentGraph G sites) m d) :
    lpReplicaCurrentReflect x ∈
      lpReplicaTripleSeamGhostSource sites i j k := by
  have hsame := lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites
    G sites hsite d.1 huv hfold
  have hsiteMem (t : I) (ht : t = i ∨ t = j ∨ t = k) :
      sites t = sites i ∨ sites t = sites j ∨ sites t = sites k := by
    rcases ht with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hsame with ⟨p, r, hd⟩ | ⟨p, r, hd⟩
  · have hpr : (s(Sum.inl p, Sum.inl r) : Sym2 (V ⊕ Unit)) =
        s(Sum.inl (sites u), Sum.inl (sites v)) := by
      unfold lpReplicaCurrentFoldedEdge at hfold
      change Sym2.map lpReplicaCurrentFold d.1.1 = _ at hfold
      rw [hd, Sym2.map_mk] at hfold
      simpa [lpReplicaCurrentFold] using hfold
    rw [Sym2.eq_iff] at hpr
    simp only [Sum.inl.injEq] at hpr
    change x ∈ d.1.1 at hx
    rw [hd, Sym2.mem_iff] at hx
    rcases hpr with hpr | hpr <;> rcases hx with rfl | rfl
    · apply (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk p).mpr
      rw [hpr.1]
      exact hsiteMem u hu
    · apply (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk r).mpr
      rw [hpr.2]
      exact hsiteMem v hv
    · apply (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk p).mpr
      rw [hpr.1]
      exact hsiteMem v hv
    · apply (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk r).mpr
      rw [hpr.2]
      exact hsiteMem u hu
  · have hpr : (s(Sum.inl p, Sum.inl r) : Sym2 (V ⊕ Unit)) =
        s(Sum.inl (sites u), Sum.inl (sites v)) := by
      unfold lpReplicaCurrentFoldedEdge at hfold
      change Sym2.map lpReplicaCurrentFold d.1.1 = _ at hfold
      rw [hd, Sym2.map_mk] at hfold
      simpa [lpReplicaCurrentFold] using hfold
    rw [Sym2.eq_iff] at hpr
    simp only [Sum.inl.injEq] at hpr
    change x ∈ d.1.1 at hx
    rw [hd, Sym2.mem_iff] at hx
    rcases hpr with hpr | hpr <;> rcases hx with rfl | rfl
    · apply (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk p).mpr
      rw [hpr.1]
      exact hsiteMem u hu
    · apply (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk r).mpr
      rw [hpr.2]
      exact hsiteMem v hv
    · apply (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk p).mpr
      rw [hpr.1]
      exact hsiteMem v hv
    · apply (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk r).mpr
      rw [hpr.2]
      exact hsiteMem u hu



theorem lpReplica_strictPhysicalRoute_disjoint_reflected_ends
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {u v : I} (huv : u ≠ v)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    Disjoint
      (endsM (lpReplicaCurrentGraph G sites) m d).toFinset
      (Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset := by
  rw [Finset.disjoint_left]
  intro x hx hxr
  have hsame := lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites
    G sites hsite d.1 huv hfold
  rcases hsame with ⟨p, r, hd⟩ | ⟨p, r, hd⟩ <;>
    rw [Sym2.mem_toFinset] at hx <;>
    change x ∈ d.1.1 at hx <;>
    rw [hd, Sym2.mem_iff] at hx <;>
    rw [Sym2.mem_toFinset, Sym2.mem_map] at hxr <;>
    rcases hxr with ⟨y, hy, hyx⟩ <;>
    change y ∈ d.1.1 at hy <;>
    rw [hd, Sym2.mem_iff] at hy <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [lpReplicaCurrentReflect] at hyx



theorem lpReplica_partialReflect_strictMatchingRoute_doubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (B : Finset (LPReplicaCurrentVertex V))
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hunique : ∀ x ∈ B,
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hreflectedSupport : ∀ x ∈
      endsM (lpReplicaCurrentGraph G sites) m d,
      lpReplicaCurrentReflect x ∈ B)
    (hdisjoint : Disjoint
      (endsM (lpReplicaCurrentGraph G sites) m d).toFinset
      (Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    let d' := R d
    let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K
    d' ∈ K' ∧
      (∀ x ∈ endsM (lpReplicaCurrentGraph G sites) target d',
        ∃ e' ∈ K', e' ≠ d' ∧
          x ∈ endsM (lpReplicaCurrentGraph G sites) target e') := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let E := endsM H m
  let target := lpReplicaCollisionProfile G sites
    (profileFlux H m (Finset.univ \ {d}))
    (profileFlux H m {d})
  let E' := endsM H target
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let d' := R d
  let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K
  have hd'K' : d' ∈ K' := by
    exact Finset.mem_map.mpr ⟨d, hdK, rfl⟩
  refine ⟨hd'K', ?_⟩
  intro x hxd'
  have hd'ends : E' d' = Sym2.map lpReplicaCurrentReflect (E d) := by
    simpa only [E', E, d', R, target, H] using
      (lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
        G sites m {d} d (by simp))
  change x ∈ E' d' at hxd'
  rw [hd'ends, Sym2.mem_map] at hxd'
  obtain ⟨y, hyd, hry⟩ := hxd'
  have hxB : x ∈ B := by
    rw [← hry]
    exact hreflectedSupport y hyd
  obtain ⟨e, ⟨heK, hxe⟩, _⟩ := hunique x hxB
  have hed : e ≠ d := by
    intro hed
    subst e
    apply Finset.disjoint_left.mp hdisjoint
    · exact hxe
    · exact Sym2.mem_toFinset.mpr
        (by rw [Sym2.mem_map]; exact ⟨y, hyd, hry⟩)
  let e' := R e
  have he'K' : e' ∈ K' := Finset.mem_map.mpr ⟨e, heK, rfl⟩
  have he'd' : e' ≠ d' := fun h => hed (R.injective h)
  have he'ends : E' e' = E e := by
    simpa only [E', E, e', R, target, H] using
      (lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
        G sites m {d} e (by simpa using hed))
  exact ⟨e', he'K', he'd', by
    change x ∈ E' e'
    rw [he'ends]
    exact Sym2.mem_toFinset.mp hxe⟩


def LPReplicaStrictPhysicalDoubleIncidenceRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) : Prop :=
  ∃ d ∈ K,
    ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag ∧
      ∀ x ∈ endsM (lpReplicaCurrentGraph G sites) m d,
        ∃ e ∈ K, e ≠ d ∧
          x ∈ endsM (lpReplicaCurrentGraph G sites) m e


theorem lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {u v : I} (huv : u ≠ v)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (B : Finset (LPReplicaCurrentVertex V))
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hunique : ∀ x ∈ B,
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hreflectedSupport : ∀ x ∈
      endsM (lpReplicaCurrentGraph G sites) m d,
      lpReplicaCurrentReflect x ∈ B)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hdisjoint : Disjoint
      (endsM (lpReplicaCurrentGraph G sites) m d).toFinset
      (Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    LPReplicaStrictPhysicalDoubleIncidenceRaw G sites target
      (lpReplicaPartialReflectCopiesRaw G sites m {d} K) := by
  classical
  dsimp only
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ {d}))
    (profileFlux (lpReplicaCurrentGraph G sites) m {d})
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let d' := R d
  let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K
  have hincidence :=
    lpReplica_partialReflect_strictMatchingRoute_doubleIncidence
      G sites m K B d hdK hunique hreflectedSupport hdisjoint
  change d' ∈ K' ∧
      ∀ x ∈ endsM (lpReplicaCurrentGraph G sites) target d',
        ∃ e' ∈ K', e' ≠ d' ∧
          x ∈ endsM (lpReplicaCurrentGraph G sites) target e' at hincidence
  have hd'edge : d'.1 = lpReplicaCurrentEdgeReflect G sites d.1 := by
    simpa only [d', R, Finset.mem_singleton, ↓reduceIte] using
      (lpReplicaPartialReflectCopyEquivRaw_edge G sites m {d} d)
  have hd'nondiag :
      ¬ (lpReplicaCurrentFoldedEdge G sites d'.1).IsDiag := by
    rw [hd'edge, lpReplicaCurrentFoldedEdge_reflect, hfold,
      Sym2.mk_isDiag_iff]
    exact fun h => hsite.ne huv (Sum.inl.inj h)
  exact ⟨d', hincidence.1, hd'nondiag, hincidence.2⟩



def LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) : Prop :=
  let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
    G sites A B q z
  let tag := lpReplicaOrientedFourColorTag G sites A B q oz
  let K := lpReplicaRowCopies G sites oz.1.1 tag true
  LPReplicaStrictPhysicalDoubleIncidenceRaw G sites oz.1.1 K


def LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  match y with
  | Sum.inl z =>
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z
  | Sum.inr z =>
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z


def LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
    G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) y.2.1)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) y.2.2.1 ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q y.2.2.2



theorem LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {B C : Finset (LPReplicaCurrentVertex V)} (h : B = C)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites A C q
        (cast (congrArg
          (fun D => LPReplicaDecoratedOrbitAtom G sites A D q) h) z) ↔
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites A B q z := by
  subst C
  rfl

end

end StatMech.Ising
