/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalInterval
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Simplices of the finite Joyal interval

The two horn attachments retain the old simplices and freely add the
simplices outside the attaching horn. The degreewise pushout description
will identify the actual nondegenerate generators.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet

section PushoutComplement

variable {X Y : SSet.{u}} (A : Y.Subcomplex) (f : A.toSSet ⟶ X)

private lemma eval_pushout (m : SimplexCategoryᵒᵖ) :
    IsPushout (f.app m) (A.ι.app m)
      ((pushout.inl f A.ι).app m) ((pushout.inr f A.ι).app m) :=
  (IsPushout.of_hasPushout f A.ι).map ((evaluation _ _).obj m)

private noncomputable def normalRight (m : SimplexCategoryᵒᵖ) (y : Y.obj m) :
    X.obj m ⊕ {y : Y.obj m // y ∉ A.obj m} := by
  classical
  exact if hy : y ∈ A.obj m then Sum.inl (f.app m ⟨y, hy⟩) else Sum.inr ⟨y, hy⟩

private lemma normal_compat (m : SimplexCategoryᵒᵖ) :
    f.app m ≫ (↾Sum.inl) = A.ι.app m ≫ (↾normalRight A f m) := by
  classical
  ext a
  simp [normalRight, a.property]

private noncomputable def normal (m : SimplexCategoryᵒᵖ) :
    (pushout f A.ι).obj m ⟶ (X.obj m ⊕ {y : Y.obj m // y ∉ A.obj m}) :=
  (eval_pushout A f m).desc (↾Sum.inl) (↾normalRight A f m) (normal_compat A f m)

private lemma normal_inl (m : SimplexCategoryᵒᵖ) (x : X.obj m) :
    normal A f m ((pushout.inl f A.ι).app m x) = Sum.inl x :=
  ConcreteCategory.congr_hom
    ((eval_pushout A f m).inl_desc (↾Sum.inl) (↾normalRight A f m)
      (normal_compat A f m)) x

private lemma normal_inr (m : SimplexCategoryᵒᵖ) (y : Y.obj m) :
    normal A f m ((pushout.inr f A.ι).app m y) = normalRight A f m y :=
  ConcreteCategory.congr_hom
    ((eval_pushout A f m).inr_desc (↾Sum.inl) (↾normalRight A f m)
      (normal_compat A f m)) y

private lemma inl_injective (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((pushout.inl f A.ι).app m) := by
  intro x y h
  simpa only [normal_inl, Sum.inl.injEq] using congrArg (normal A f m) h

private lemma mono_inl : Mono (pushout.inl f A.ι) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  exact (mono_iff_injective _).2 (inl_injective A f m)

private lemma inr_injective_of_notMem {m : SimplexCategoryᵒᵖ} {y z : Y.obj m}
    (hy : y ∉ A.obj m)
    (h : (pushout.inr f A.ι).app m y = (pushout.inr f A.ι).app m z) : y = z := by
  classical
  have h' := congrArg (normal A f m) h
  simp only [normal_inr] at h'
  by_cases hz : z ∈ A.obj m
  · simp [normalRight, hy, hz] at h'
  · simpa [normalRight, hy, hz] using h'

private lemma inr_ne_inl {m : SimplexCategoryᵒᵖ} {y : Y.obj m} (hy : y ∉ A.obj m)
    (x : X.obj m) :
    (pushout.inr f A.ι).app m y ≠ (pushout.inl f A.ι).app m x := by
  classical
  intro h
  have h' := congrArg (normal A f m) h
  simp [normal_inl, normal_inr, normalRight, hy] at h'

private lemma nonDegenerate_inr {n : ℕ} (y : Y _⦋n⦌)
    (hy : y ∉ A.obj (op ⦋n⦌)) (hnd : y ∈ Y.nonDegenerate n) :
    (pushout.inr f A.ι).app (op ⦋n⦌) y ∈ (pushout f A.ι).nonDegenerate n := by
  change _ ∉ (pushout f A.ι).degenerate n
  change y ∉ Y.degenerate n at hnd
  rintro ⟨m, hm, t, z, hz⟩
  rcases Types.eq_or_eq_of_isPushout (eval_pushout A f (op ⦋m⦌)) z with
    ⟨x, rfl⟩ | ⟨w, rfl⟩
  · have hnat :
        (pushout.inl f A.ι).app (op ⦋n⦌) (X.map t.op x) =
          (pushout f A.ι).map t.op ((pushout.inl f A.ι).app (op ⦋m⦌) x) :=
      ConcreteCategory.congr_hom ((pushout.inl f A.ι).naturality t.op) x
    exact inr_ne_inl A f hy (X.map t.op x) (hz.symm.trans hnat.symm)
  · have hnat :
        (pushout.inr f A.ι).app (op ⦋n⦌) (Y.map t.op w) =
          (pushout f A.ι).map t.op ((pushout.inr f A.ι).app (op ⦋m⦌) w) :=
      ConcreteCategory.congr_hom ((pushout.inr f A.ι).naturality t.op) w
    have heq : y = Y.map t.op w :=
      inr_injective_of_notMem A f hy (hz.symm.trans hnat.symm)
    exact hnd ⟨m, hm, t, w, heq.symm⟩

private noncomputable def ndSumMap (n : ℕ) :
    X.nonDegenerate n ⊕ {y : Y.nonDegenerate n // y.val ∉ A.obj (op ⦋n⦌)} →
      (pushout f A.ι).nonDegenerate n := by
  have : Mono (pushout.inl f A.ι) := mono_inl A f
  exact fun
    | Sum.inl x => ⟨(pushout.inl f A.ι).app _ x.val,
        (nonDegenerate_iff_of_mono _ _).2 x.property⟩
    | Sum.inr y => ⟨(pushout.inr f A.ι).app _ y.val.val,
        nonDegenerate_inr A f y.val.val y.property y.val.property⟩

private lemma ndSumMap_injective (n : ℕ) : Function.Injective (ndSumMap A f n) := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (Subtype.ext
      (inl_injective A f _ (congrArg Subtype.val h)))
  · exact (inr_ne_inl A f y.property x.val (congrArg Subtype.val h).symm).elim
  · exact (inr_ne_inl A f x.property y.val (congrArg Subtype.val h)).elim
  · exact congrArg Sum.inr (Subtype.ext (Subtype.ext
      (inr_injective_of_notMem A f x.property (congrArg Subtype.val h))))

private lemma ndSumMap_surjective (n : ℕ) : Function.Surjective (ndSumMap A f n) := by
  intro z
  rcases Types.eq_or_eq_of_isPushout' (eval_pushout A f (op ⦋n⦌)) z.val with
    ⟨x, hx⟩ | ⟨y, hy, hout⟩
  · have hnd : x ∈ X.nonDegenerate n :=
      nonDegenerate_of_app_apply (pushout.inl f A.ι) (by rw [hx]; exact z.property)
    exact ⟨Sum.inl ⟨x, hnd⟩, Subtype.ext hx⟩
  · have hnot : y ∉ A.obj (op ⦋n⦌) := by
      intro h
      exact hout ⟨⟨y, h⟩, rfl⟩
    have hnd : y ∈ Y.nonDegenerate n :=
      nonDegenerate_of_app_apply (pushout.inr f A.ι) (by rw [hy]; exact z.property)
    exact ⟨Sum.inr ⟨⟨y, hnd⟩, hnot⟩, Subtype.ext hy⟩

private noncomputable def ndSumEquiv (n : ℕ) :
    (pushout f A.ι).nonDegenerate n ≃
      (X.nonDegenerate n ⊕ {y : Y.nonDegenerate n // y.val ∉ A.obj (op ⦋n⦌)}) :=
  (Equiv.ofBijective (ndSumMap A f n)
    ⟨ndSumMap_injective A f n, ndSumMap_surjective A f n⟩).symm

end PushoutComplement

section HornCells

private abbrev hornND (i : Fin 3) (n : ℕ) : Type u :=
  {y : (Δ[2] : SSet.{u}).nonDegenerate n // y.val ∉ Λ[2, i].obj (op ⦋n⦌)}

private def edgeCell (i : Fin 3) : hornND.{u} i 1 :=
  ⟨⟨stdSimplex.objEquiv.symm (SimplexCategory.δ i), by
      rw [stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono]
      infer_instance⟩, (objEquiv_symm_δ_notMem_horn_iff i i).2 rfl⟩

private def topCell (i : Fin 3) : hornND.{u} i 2 :=
  ⟨⟨stdSimplex.objEquiv.symm (𝟙 ⦋2⦌), stdSimplex.objEquiv_symm_id_mem_nonDegenerate 2⟩,
    objEquiv_symm_notMem_horn_of_isIso i (𝟙 ⦋2⦌)⟩

private lemma hornND_zero_empty (i : Fin 3) : IsEmpty (hornND.{u} i 0) where
  false x := x.property (by simp [horn_obj_zero])

private lemma edgeCell_unique (i : Fin 3) (x : hornND.{u} i 1) : x = edgeCell i := by
  classical
  let S := stdSimplex.nonDegenerateEquiv' x.val
  have hcard : S.val.card = 2 := S.property
  have hnot : ¬ stdSimplex.face S.val ≤ Λ[2, i] := by
    rw [stdSimplex.face_nonDegenerateEquiv']
    rw [Subcomplex.ofSimplex_le_iff]
    exact x.property
  rw [face_le_horn_iff] at hnot
  have hneq : S.val ≠ .univ := by
    intro h
    rw [h] at hcard
    norm_num at hcard
  have heq : S.val = {i}ᶜ := by tauto
  have hcomplex : Subcomplex.ofSimplex x.val.val =
      Subcomplex.ofSimplex (edgeCell i).val.val := by
    calc
      Subcomplex.ofSimplex x.val.val = stdSimplex.face S.val :=
        (stdSimplex.face_nonDegenerateEquiv' x.val).symm
      _ = stdSimplex.face {i}ᶜ := congrArg stdSimplex.face heq
      _ = Subcomplex.ofSimplex (edgeCell i).val.val :=
        stdSimplex.face_singleton_compl i
  have hN : N.mk x.val.val x.val.property =
      N.mk (edgeCell i).val.val (edgeCell i).val.property :=
    N.subcomplex_injective hcomplex
  apply Subtype.ext
  apply Subtype.ext
  rw [N.ext_iff, SSet.S.ext_iff'] at hN
  rcases hN with ⟨h, hs⟩
  cases h
  exact hs

private lemma topCell_unique (i : Fin 3) (x : hornND.{u} i 2) : x = topCell i := by
  apply Subtype.ext
  apply Subtype.ext
  have h := x.val.property
  simp only [stdSimplex.nonDegenerate_top_dim, Set.mem_singleton_iff] at h
  exact h

private noncomputable def edgeCellEquiv (i : Fin 3) : hornND.{u} i 1 ≃ Fin 1 := by
  letI : Unique (hornND.{u} i 1) := { default := edgeCell i, uniq := edgeCell_unique i }
  exact Equiv.ofUnique _ _

private noncomputable def topCellEquiv (i : Fin 3) : hornND.{u} i 2 ≃ Fin 1 := by
  letI : Unique (hornND.{u} i 2) := { default := topCell i, uniq := topCell_unique i }
  exact Equiv.ofUnique _ _

private def baseEdge : (Δ[1] : SSet.{u}).nonDegenerate 1 :=
  ⟨stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), stdSimplex.objEquiv_symm_id_mem_nonDegenerate 1⟩

private lemma baseEdge_unique (x : (Δ[1] : SSet.{u}).nonDegenerate 1) : x = baseEdge := by
  apply Subtype.ext
  have h := x.property
  simp only [stdSimplex.nonDegenerate_top_dim, Set.mem_singleton_iff] at h
  exact h

private noncomputable def baseEdgeEquiv : (Δ[1] : SSet.{u}).nonDegenerate 1 ≃ Fin 1 := by
  letI : Unique ((Δ[1] : SSet.{u}).nonDegenerate 1) :=
    { default := baseEdge, uniq := baseEdge_unique }
  exact Equiv.ofUnique _ _

end HornCells

namespace joyalInterval

instance finite_leftObj : SSet.Finite leftObj.{u} := by
  change SSet.Finite (pushout leftAttach.{u} Λ[2, 0].ι)
  apply finite_of_isColimit (IsPushout.of_hasPushout leftAttach.{u} Λ[2, 0].ι).isColimit
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

instance finite : SSet.Finite joyalInterval.{u} := by
  change SSet.Finite (pushout rightAttach.{u} Λ[2, 2].ι)
  apply finite_of_isColimit (IsPushout.of_hasPushout rightAttach.{u} Λ[2, 2].ι).isColimit
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

instance dimension_leftObj : HasDimensionLT leftObj.{u} 3 := by
  have : HasDimensionLT (Δ[1] : SSet.{u}) 3 :=
    hasDimensionLT_of_le (X := Δ[1]) (d := 2) 3 (by decide)
  change HasDimensionLT (pushout leftAttach.{u} Λ[2, 0].ι) 3
  apply hasDimensionLT_of_isColimit
    (IsPushout.of_hasPushout leftAttach.{u} Λ[2, 0].ι).isColimit
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

instance dimension : HasDimensionLT joyalInterval.{u} 3 := by
  change HasDimensionLT (pushout rightAttach.{u} Λ[2, 2].ι) 3
  apply hasDimensionLT_of_isColimit
    (IsPushout.of_hasPushout rightAttach.{u} Λ[2, 2].ι).isColimit
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

instance mono_forward : Mono forward.{u} := by
  have hL : Mono forwardLeft.{u} := mono_inl Λ[2, 0] leftAttach.{u}
  have hR : Mono (pushout.inl rightAttach.{u} Λ[2, 2].ι) :=
    mono_inl Λ[2, 2] rightAttach.{u}
  dsimp only [forward]
  refine ⟨fun g h w => ?_⟩
  apply hL.right_cancellation g h
  apply hR.right_cancellation (g ≫ forwardLeft.{u}) (h ≫ forwardLeft.{u})
  simpa only [joyalInterval, Category.assoc] using w

/-- The two retained vertices of the actual finite interval. -/
noncomputable def vertex (ε : Fin 2) : joyalInterval.{u} _⦋0⦌ :=
  forward.{u}.app _ (stdSimplex.obj₀Equiv.symm ε)

private lemma vertex_bijective : Function.Bijective vertex.{u} := by
  constructor
  · intro a b h
    exact stdSimplex.obj₀Equiv.symm.injective
      ((injective_of_mono (forward.{u}.app _)) h)
  · intro p
    rcases Types.eq_or_eq_of_isPushout' (eval_pushout Λ[2, 2] rightAttach.{u} (op ⦋0⦌)) p
      with ⟨x, hx⟩ | ⟨y, hy, hout⟩
    · rcases Types.eq_or_eq_of_isPushout'
        (eval_pushout Λ[2, 0] leftAttach.{u} (op ⦋0⦌)) x
        with ⟨z, hz⟩ | ⟨y, hy, hout⟩
      · refine ⟨stdSimplex.obj₀Equiv z, ?_⟩
        change (pushout.inl rightAttach.{u} Λ[2, 2].ι).app _
          ((pushout.inl leftAttach.{u} Λ[2, 0].ι).app _
            (stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv z))) = p
        simpa only [Equiv.symm_apply_apply, hz] using hx
      · exact (hout ⟨⟨y, by simp [horn_obj_zero]⟩, rfl⟩).elim
    · exact (hout ⟨⟨y, by simp [horn_obj_zero]⟩, rfl⟩).elim

/-- Exact enumeration of the two vertices, with source indexed by zero. -/
@[no_expose]
noncomputable def verticesEquiv : Fin 2 ≃ joyalInterval.{u} _⦋0⦌ :=
  Equiv.ofBijective vertex vertex_bijective

private noncomputable def leftEdgesEquiv : leftObj.{u}.nonDegenerate 1 ≃ Fin 2 :=
  (ndSumEquiv Λ[2, 0] leftAttach.{u} 1).trans
    ((Equiv.sumCongr baseEdgeEquiv (edgeCellEquiv 0)).trans finSumFinEquiv)

/-- Exact enumeration of the forward, left-inverse and right-inverse edges. -/
@[no_expose]
noncomputable def nonDegenerateEdgesEquiv : Fin 3 ≃ joyalInterval.{u}.nonDegenerate 1 :=
  ((ndSumEquiv Λ[2, 2] rightAttach.{u} 1).trans
    ((Equiv.sumCongr leftEdgesEquiv (edgeCellEquiv 2)).trans finSumFinEquiv)).symm

private noncomputable def leftTriangleND : leftObj.{u}.nonDegenerate 2 :=
  ndSumMap Λ[2, 0] leftAttach.{u} 2 (Sum.inr (topCell 0))

private lemma leftTriangleND_unique (x : leftObj.{u}.nonDegenerate 2) : x = leftTriangleND := by
  rcases ndSumMap_surjective Λ[2, 0] leftAttach.{u} 2 x with ⟨y | y, hy⟩
  · have h := y.property
    have he : (Δ[1] : SSet.{u}).nonDegenerate 2 = ∅ :=
      (Δ[1] : SSet.{u}).nonDegenerate_eq_empty_of_hasDimensionLT 2 2
    simp only [he, Set.notMem_empty] at h
  · rw [topCell_unique 0 y] at hy
    exact hy.symm

private noncomputable def leftTriangleEquiv : leftObj.{u}.nonDegenerate 2 ≃ Fin 1 := by
  letI : Unique (leftObj.{u}.nonDegenerate 2) :=
    { default := leftTriangleND, uniq := leftTriangleND_unique }
  exact Equiv.ofUnique _ _

/-- Exact enumeration of the two full unit triangles. -/
@[no_expose]
noncomputable def nonDegenerateTrianglesEquiv : Fin 2 ≃ joyalInterval.{u}.nonDegenerate 2 :=
  ((ndSumEquiv Λ[2, 2] rightAttach.{u} 2).trans
    ((Equiv.sumCongr leftTriangleEquiv (topCellEquiv 2)).trans finSumFinEquiv)).symm

lemma verticesEquiv_apply (ε : Fin 2) : verticesEquiv.{u} ε = vertex ε := by rfl

lemma nonDegenerateEdgesEquiv_zero :
    (nonDegenerateEdgesEquiv.{u} 0).val =
      forward.{u}.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by rfl

lemma nonDegenerateEdgesEquiv_one :
    (nonDegenerateEdgesEquiv.{u} 1).val =
      leftInverse.{u}.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by rfl

lemma nonDegenerateEdgesEquiv_two :
    (nonDegenerateEdgesEquiv.{u} 2).val =
      rightInverse.{u}.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by rfl

lemma nonDegenerateTrianglesEquiv_zero :
    (nonDegenerateTrianglesEquiv.{u} 0).val =
      leftTriangle.{u}.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋2⦌)) := by rfl

lemma nonDegenerateTrianglesEquiv_one :
    (nonDegenerateTrianglesEquiv.{u} 1).val =
      rightTriangle.{u}.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋2⦌)) := by rfl

theorem card_vertices : Nat.card (joyalInterval.{u} _⦋0⦌) = 2 := by
  simpa using (Nat.card_congr verticesEquiv.{u}).symm

theorem card_nonDegenerate_edges : Nat.card (joyalInterval.{u}.nonDegenerate 1) = 3 := by
  simpa using (Nat.card_congr nonDegenerateEdgesEquiv.{u}).symm

theorem card_nonDegenerate_triangles : Nat.card (joyalInterval.{u}.nonDegenerate 2) = 2 := by
  simpa using (Nat.card_congr nonDegenerateTrianglesEquiv.{u}).symm

theorem nonDegenerate_eq_empty (n : ℕ) (hn : 2 < n) :
    joyalInterval.{u}.nonDegenerate n = ∅ :=
  joyalInterval.{u}.nonDegenerate_eq_empty_of_hasDimensionLT 3 n (by lia)

private lemma std_endpoints_ne (n : ℕ) (a b : (Δ[0] : SSet.{u}) _⦋n⦌) :
    (stdSimplex.δ (1 : Fin 2)).app _ a ≠ (stdSimplex.δ (0 : Fin 2)).app _ b := by
  intro h
  have h' := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋n⦌ => x 0) h
  change Fin.succAbove (1 : Fin 2) (a 0) = Fin.succAbove (0 : Fin 2) (b 0) at h'
  have ha : a 0 = 0 := Fin.eq_zero _
  have hb : b 0 = 0 := Fin.eq_zero _
  rw [ha, hb] at h'
  exact (by decide : (0 : Fin 2) ≠ 1) h'

private lemma endpoint_app_ne (n : ℕ) (a b : (Δ[0] : SSet.{u}) _⦋n⦌) :
    (endpoint.{u} 0).app _ a ≠ (endpoint.{u} 1).app _ b := by
  intro h
  have h' : (stdSimplex.δ (1 : Fin 2)).app _ a =
      (stdSimplex.δ (0 : Fin 2)).app _ b := by
    apply injective_of_mono (forward.{u}.app (op ⦋n⦌))
    simpa only [endpoint_zero, endpoint_one, NatTrans.comp_app_apply] using h
  exact std_endpoints_ne n a b h'

/-- The source and target vertex subcomplexes have disjoint images. -/
theorem endpoint_images_disjoint :
    Disjoint (Subcomplex.range (endpoint.{u} 0)) (Subcomplex.range (endpoint.{u} 1)) := by
  rw [disjoint_iff]
  ext m x
  obtain ⟨⟨n⟩⟩ := m
  change ((∃ a, (endpoint.{u} 0).app (op ⦋n⦌) a = x) ∧
    ∃ b, (endpoint.{u} 1).app (op ⦋n⦌) b = x) ↔ False
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact endpoint_app_ne n a b (ha.trans hb.symm)
  · exact False.elim

/-- The map from the coproduct of the two endpoints into the finite interval. -/
noncomputable def endpointCoprod :
    (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ joyalInterval.{u} :=
  coprod.desc (endpoint 0) (endpoint 1)

@[reassoc (attr := simp)]
lemma inl_endpointCoprod : coprod.inl ≫ endpointCoprod.{u} = endpoint 0 :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_endpointCoprod : coprod.inr ≫ endpointCoprod.{u} = endpoint 1 :=
  coprod.inr_desc _ _

private lemma exists_coprod_app (n : ℕ)
    (x : ((Δ[0] : SSet.{u}) ⨿ Δ[0]) _⦋n⦌) :
    (∃ a, (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app _ a = x) ∨
      ∃ b, (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app _ b = x := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)
  have hc := isColimitOfPreserves E (coprodIsCoprod (Δ[0] : SSet.{u}) Δ[0])
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hc x
  rcases i with ⟨_ | _⟩
  · exact Or.inl ⟨a, ha⟩
  · exact Or.inr ⟨a, ha⟩

instance mono_endpointCoprod : Mono endpointCoprod.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  have hL (a : (Δ[0] : SSet.{u}) _⦋n⦌) :
      endpointCoprod.{u}.app _
        ((coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app (op ⦋n⦌) a) =
          (endpoint 0).app _ a :=
    ConcreteCategory.congr_hom (NatTrans.congr_app inl_endpointCoprod.{u} (op ⦋n⦌)) a
  have hR (a : (Δ[0] : SSet.{u}) _⦋n⦌) :
      endpointCoprod.{u}.app _
        ((coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app (op ⦋n⦌) a) =
          (endpoint 1).app _ a :=
    ConcreteCategory.congr_hom (NatTrans.congr_app inr_endpointCoprod.{u} (op ⦋n⦌)) a
  intro x y h
  rcases exists_coprod_app n x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases exists_coprod_app n y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have hab : a = b := by
        ext i
        exact congrArg Fin.val ((Fin.eq_zero (a i)).trans (Fin.eq_zero (b i)).symm)
      exact congrArg
        ((coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app (op ⦋n⦌)) hab
    · exact (endpoint_app_ne n a b (by simpa only [hL, hR] using h)).elim
  · rcases exists_coprod_app n y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact (endpoint_app_ne n b a (by simpa only [hL, hR] using h.symm)).elim
    · have hab : a = b := by
        ext i
        exact congrArg Fin.val ((Fin.eq_zero (a i)).trans (Fin.eq_zero (b i)).symm)
      exact congrArg
        ((coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]).app (op ⦋n⦌)) hab

end joyalInterval

end SSet
