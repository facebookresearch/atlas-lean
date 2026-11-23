/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import MathlibExt.Topology.Homotopy.StrictLoopMap

/-!
# The loop-space shift for cube-based homotopy groups

This file constructs the multiplicative equivalence between the positive
homotopy groups of a loop space and the next homotopy groups of the original
space.  It also provides an equality-aware map on positive homotopy groups,
needed when a continuous map preserves a basepoint by a specified equality.

The comparison is entirely topological and cube-based.  No singular,
weak-equivalence, derived-loop, spectrum, or model-category comparison is
asserted here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

universe u v w z

namespace HomotopyGroup

/-- The map on positive cube-based homotopy groups induced by a continuous
map whose value at the source basepoint is propositionally the target
basepoint. -/
def mapHomOfEq
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x →ₙ*
      HomotopyGroup.Pi (n + 1) Y y := by
  subst y
  exact (HomotopyGroup.mapHom f).toMulHom

/-- The equality-aware map has the same underlying function as postcomposition. -/
@[simp]
theorem mapHomOfEq_apply
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    mapHomOfEq f h n a = h ▸ HomotopyGroup.map f a := by
  subst y
  rfl

/-- The equality-aware map induced by the identity fixes every class. -/
@[simp]
theorem mapHomOfEq_id
    {X : Type u} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    mapHomOfEq (ContinuousMap.id X) rfl n a = a := by
  rw [mapHomOfEq_apply, HomotopyGroup.map_id]

/-- Equality-aware maps respect source-first composition. -/
theorem mapHomOfEq_comp
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z}
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : f x = y) (hg : g y = z) (hfg : (g.comp f) x = z)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    mapHomOfEq (g.comp f) hfg n a =
      mapHomOfEq g hg n (mapHomOfEq f hf n a) := by
  subst y
  subst z
  simpa only [mapHomOfEq_apply] using HomotopyGroup.map_comp f g a

end HomotopyGroup

namespace GenLoop

/-- One-dimensional generalized loops are homeomorphic to ordinary based
loops. -/
def finOneHomeomorphLoopSpace
    (X : Type u) [TopologicalSpace X] (x : X) :
    GenLoop (Fin 1) X x ≃ₜ LoopSpace X x where
  toEquiv := genLoopEquivOfUnique (Fin 1)
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))

end GenLoop

namespace HomotopyGroup

private def finOneMapMulEquiv
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x) ≃*
      HomotopyGroup.Pi (n + 1) (GenLoop (Fin 1) X x) GenLoop.const := by
  let e := GenLoop.finOneHomeomorphLoopSpace X x
  have hconst : e GenLoop.const = Path.refl x := by
    apply Path.ext
    rfl
  have hrefl : e.symm (Path.refl x) = GenLoop.const := by
    apply GenLoop.ext
    intro y
    rfl
  let ef : C(GenLoop (Fin 1) X x, LoopSpace X x) :=
    ⟨e, e.continuous_toFun⟩
  let ei : C(LoopSpace X x, GenLoop (Fin 1) X x) :=
    ⟨e.symm, e.continuous_invFun⟩
  let forward := mapHomOfEq ei hrefl n
  let inverse := mapHomOfEq ef hconst n
  refine MulEquiv.ofBijective forward ?_
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inverse, ?_, ?_⟩
  · intro a
    change mapHomOfEq ef hconst n (mapHomOfEq ei hrefl n a) = a
    have hcomp :
        (ef.comp ei) (Path.refl x) =
          Path.refl x := by
      change e (e.symm (Path.refl x)) = Path.refl x
      exact e.apply_symm_apply (Path.refl x)
    calc
      inverse (forward a) =
          mapHomOfEq (ef.comp ei)
            hcomp n a :=
        (mapHomOfEq_comp ei ef
          hrefl hconst hcomp n a).symm
      _ = a := by
        have heq : ef.comp ei = ContinuousMap.id _ := by
          apply ContinuousMap.ext
          exact e.apply_symm_apply
        rw [mapHomOfEq_apply]
        cases heq
        exact HomotopyGroup.map_id a
  · intro a
    change mapHomOfEq ei hrefl n (mapHomOfEq ef hconst n a) = a
    have hcomp :
        (ei.comp ef) GenLoop.const =
          GenLoop.const := by
      change e.symm (e GenLoop.const) = GenLoop.const
      exact e.symm_apply_apply GenLoop.const
    calc
      forward (inverse a) =
          mapHomOfEq (ei.comp ef)
            hcomp n a :=
        (mapHomOfEq_comp ef ei
          hconst hrefl hcomp n a).symm
      _ = a := by
        obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
        have normalize
            (y : GenLoop (Fin 1) X x)
            (hy : (ei.comp ef) GenLoop.const = y) :
            mapHomOfEq (ei.comp ef) hy n (HomotopyGroup.mk p) =
              HomotopyGroup.mk
                (⟨(GenLoop.map (ei.comp ef) p).1,
                  fun t ht =>
                    (GenLoop.boundary (GenLoop.map (ei.comp ef) p) t ht).trans hy⟩ :
                  GenLoop (Fin (n + 1)) (GenLoop (Fin 1) X x) y) := by
          subst y
          rfl
        rw [normalize GenLoop.const hcomp]
        apply congrArg HomotopyGroup.mk
        apply GenLoop.ext
        intro t
        exact e.symm_apply_apply (p t)

private theorem flattenHomotopic
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] {x : X}
    (p q : GenLoop M (GenLoop N X x) GenLoop.const) :
    GenLoop.Homotopic p q ↔
      GenLoop.Homotopic
        (GenLoop.genLoopGenLoopEquiv x p)
        (GenLoop.genLoopGenLoopEquiv x q) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{
      toFun := fun ty =>
        H (ty.1, ty.2 ∘ Sum.inl) (ty.2 ∘ Sum.inr)
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro y
      change H (0, y ∘ Sum.inl) (y ∘ Sum.inr) =
        p (y ∘ Sum.inl) (y ∘ Sum.inr)
      rw [H.apply_zero]
      rfl
    · intro y
      change H (1, y ∘ Sum.inl) (y ∘ Sum.inr) =
        q (y ∘ Sum.inl) (y ∘ Sum.inr)
      rw [H.apply_one]
      rfl
    · intro t y hy
      change H (t, y ∘ Sum.inl) (y ∘ Sum.inr) =
        p (y ∘ Sum.inl) (y ∘ Sum.inr)
      rcases Cube.boundary_sum_iff.mp hy with hM | hN
      · rw [H.eq_fst t hM]
        rfl
      · exact
          (GenLoop.boundary (H (t, y ∘ Sum.inl)) (y ∘ Sum.inr) hN).trans
            (GenLoop.boundary (p (y ∘ Sum.inl)) (y ∘ Sum.inr) hN).symm
  · rintro ⟨K⟩
    refine ⟨{
      toFun := fun ta =>
        ⟨⟨fun b =>
            K (ta.1,
              Homeomorph.sumArrowHomeomorphProdArrow.symm (ta.2, b)), by
            exact K.continuous.comp
              (continuous_const.prodMk
                (Homeomorph.sumArrowHomeomorphProdArrow.continuous_invFun.comp
                  (continuous_const.prodMk continuous_id)))⟩,
          fun b hb =>
            (K.eq_fst ta.1 (Cube.boundary_sum_iff.mpr (Or.inr (by
              simpa [Homeomorph.sumArrowHomeomorphProdArrow,
                Equiv.sumArrowEquivProdArrow] using hb)))).trans
              (GenLoop.boundary (p ta.2) b hb)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact K.continuous.comp
          ((continuous_fst.comp continuous_fst).prodMk
            (Homeomorph.sumArrowHomeomorphProdArrow.continuous_invFun.comp
              ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro a
      apply GenLoop.ext
      intro b
      change K (0, Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b)) = p a b
      simpa [GenLoop.genLoopGenLoopEquiv, GenLoop.uncurry,
        Homeomorph.sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow,
        Function.comp_def] using
        K.apply_zero (Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b))
    · intro a
      apply GenLoop.ext
      intro b
      change K (1, Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b)) = q a b
      simpa [GenLoop.genLoopGenLoopEquiv, GenLoop.uncurry,
        Homeomorph.sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow] using
        K.apply_one (Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b))
    · intro t a ha
      apply GenLoop.ext
      intro b
      change K (t, Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b)) = p a b
      have h := K.eq_fst t ((Cube.boundary_sum_iff
        (M := M) (N := N)
        (y := Homeomorph.sumArrowHomeomorphProdArrow.symm (a, b))).mpr
          (Or.inl (by
            simpa [Homeomorph.sumArrowHomeomorphProdArrow,
              Equiv.sumArrowEquivProdArrow] using ha)))
      convert h using 1
      change p a b = p a b
      rfl

private def homotopyGroupFlattenEquiv
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] (x : X) :
    HomotopyGroup M (GenLoop N X x) GenLoop.const ≃
      HomotopyGroup (M ⊕ N) X x :=
  Quotient.congr (GenLoop.genLoopGenLoopEquiv x).toEquiv
    (fun p q => flattenHomotopic p q)

private theorem flatten_transAt
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] [DecidableEq M] [DecidableEq N] {x : X}
    (i : M) (p q : GenLoop M (GenLoop N X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv x (GenLoop.transAt i q p) =
      GenLoop.transAt (Sum.inl i)
        (GenLoop.genLoopGenLoopEquiv x q)
        (GenLoop.genLoopGenLoopEquiv x p) := by
  apply GenLoop.ext
  intro y
  change (GenLoop.transAt i q p) (y ∘ Sum.inl) (y ∘ Sum.inr) =
    GenLoop.transAt (Sum.inl i)
      (GenLoop.genLoopGenLoopEquiv x q)
      (GenLoop.genLoopGenLoopEquiv x p) y
  have update_inl (v : I) :
      Function.update y (Sum.inl i) v ∘ Sum.inl =
        Function.update (y ∘ Sum.inl) i v := by
    funext j
    simp [Function.update_apply]
  have update_inr (v : I) :
      Function.update y (Sum.inl i) v ∘ Sum.inr = y ∘ Sum.inr := by
    funext j
    simp
  have eval_update
      (r : GenLoop M (GenLoop N X x) GenLoop.const) (v : I) :
      GenLoop.genLoopGenLoopEquiv x r
          (Function.update y (Sum.inl i) v) =
        r (Function.update (y ∘ Sum.inl) i v) (y ∘ Sum.inr) := by
    change r (Function.update y (Sum.inl i) v ∘ Sum.inl)
      (Function.update y (Sum.inl i) v ∘ Sum.inr) = _
    rw [update_inl, update_inr]
  simp only [GenLoop.transAt, GenLoop.coe_copy, Function.comp_apply]
  split_ifs <;> rw [eval_update]

private def homotopyGroupFlattenMulEquiv
    (M : Type w) (N : Type z) (X : Type u)
    [TopologicalSpace X] [DecidableEq M] [Nonempty M] [DecidableEq N]
    (x : X) :
    HomotopyGroup M (GenLoop N X x) GenLoop.const ≃*
      HomotopyGroup (M ⊕ N) X x where
  toEquiv := homotopyGroupFlattenEquiv x
  map_mul' := by
    intro a b
    obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
    obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
    let i := Classical.arbitrary M
    calc
      homotopyGroupFlattenEquiv x
          (HomotopyGroup.mk p * HomotopyGroup.mk q) =
        HomotopyGroup.mk
          (GenLoop.genLoopGenLoopEquiv x (GenLoop.transAt i q p)) := by
            rw [HomotopyGroup.mul_mk i p q]
            rfl
      _ = HomotopyGroup.mk
          (GenLoop.transAt (Sum.inl i)
            (GenLoop.genLoopGenLoopEquiv x q)
            (GenLoop.genLoopGenLoopEquiv x p)) :=
        congrArg HomotopyGroup.mk (flatten_transAt i p q)
      _ = HomotopyGroup.mk
          (GenLoop.transAt (Classical.arbitrary (M ⊕ N))
            (GenLoop.genLoopGenLoopEquiv x q)
            (GenLoop.genLoopGenLoopEquiv x p)) :=
        HomotopyGroup.transAt_indep (Classical.arbitrary (M ⊕ N))
          (GenLoop.genLoopGenLoopEquiv x q)
          (GenLoop.genLoopGenLoopEquiv x p)
      _ = homotopyGroupFlattenEquiv x (HomotopyGroup.mk p) *
          homotopyGroupFlattenEquiv x (HomotopyGroup.mk q) := by
        change _ =
          HomotopyGroup.mk (GenLoop.genLoopGenLoopEquiv x p) *
            HomotopyGroup.mk (GenLoop.genLoopGenLoopEquiv x q)
        rw [HomotopyGroup.mul_mk (Classical.arbitrary (M ⊕ N))]

private theorem congrHomotopic
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] {x : X} (e : M ≃ N)
    (p q : GenLoop M X x) :
    GenLoop.Homotopic p q ↔
      GenLoop.Homotopic (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  let φ := Homeomorph.piCongrLeft (Y := fun _ : N => I) e
  constructor
  · rintro ⟨H⟩
    refine ⟨{
      toFun := fun ty => H (ty.1, φ.symm ty.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk (φ.continuous_invFun.comp continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro y
      change H (0, φ.symm y) = p (φ.symm y)
      rw [H.apply_zero]
      rfl
    · intro y
      change H (1, φ.symm y) = q (φ.symm y)
      rw [H.apply_one]
      rfl
    · intro t y hy
      change H (t, φ.symm y) = p (φ.symm y)
      apply H.eq_fst t
      rcases hy with ⟨n, hn⟩
      refine ⟨e.symm n, ?_⟩
      simpa [φ, Homeomorph.piCongrLeft, Equiv.piCongrLeft] using hn
  · rintro ⟨K⟩
    refine ⟨{
      toFun := fun ty => K (ty.1, φ ty.2)
      continuous_toFun := K.continuous.comp
        (continuous_fst.prodMk (φ.continuous_toFun.comp continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro y
      change K (0, φ y) = p y
      rw [K.apply_zero]
      change p (φ.symm (φ y)) = p y
      rw [φ.symm_apply_apply]
    · intro y
      change K (1, φ y) = q y
      rw [K.apply_one]
      change q (φ.symm (φ y)) = q y
      rw [φ.symm_apply_apply]
    · intro t y hy
      change K (t, φ y) = p y
      calc
        K (t, φ y) = p (φ.symm (φ y)) := by
          apply K.eq_fst t
          rcases hy with ⟨m, hm⟩
          refine ⟨e m, ?_⟩
          simpa [φ, Homeomorph.piCongrLeft, Equiv.piCongrLeft] using hm
        _ = p y := congrArg p (φ.symm_apply_apply y)

private def homotopyGroupCongrEquiv
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] (x : X) (e : M ≃ N) :
    HomotopyGroup M X x ≃ HomotopyGroup N X x :=
  Quotient.congr (GenLoop.congr x e).toEquiv
    (fun p q => congrHomotopic e p q)

private theorem congr_transAt
    {M : Type w} {N : Type z} {X : Type u}
    [TopologicalSpace X] [DecidableEq M] [DecidableEq N] {x : X}
    (e : M ≃ N) (i : M) (p q : GenLoop M X x) :
    GenLoop.congr x e (GenLoop.transAt i q p) =
      GenLoop.transAt (e i) (GenLoop.congr x e q) (GenLoop.congr x e p) := by
  apply GenLoop.ext
  intro y
  let φ := Homeomorph.piCongrLeft (Y := fun _ : N => I) e
  change (GenLoop.transAt i q p) (φ.symm y) =
    GenLoop.transAt (e i) (GenLoop.congr x e q) (GenLoop.congr x e p) y
  have update (v : I) :
      φ.symm (Function.update y (e i) v) =
        Function.update (φ.symm y) i v := by
    funext j
    simp [φ, Homeomorph.piCongrLeft, Equiv.piCongrLeft,
      Function.update_apply]
  have eval_update (r : GenLoop M X x) (v : I) :
      GenLoop.congr x e r (Function.update y (e i) v) =
        r (Function.update (φ.symm y) i v) := by
    change r (φ.symm (Function.update y (e i) v)) = _
    rw [update]
  have coord : φ.symm y i = y (e i) := rfl
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  change (if ((y (e i) : I) : ℝ) ≤ 1 / 2 then _ else _) = _
  split_ifs <;> rw [eval_update, coord]

private def homotopyGroupCongrMulEquiv
    (M : Type w) (N : Type z) (X : Type u)
    [TopologicalSpace X]
    [DecidableEq M] [Nonempty M] [DecidableEq N] [Nonempty N]
    (x : X) (e : M ≃ N) :
    HomotopyGroup M X x ≃* HomotopyGroup N X x where
  toEquiv := homotopyGroupCongrEquiv x e
  map_mul' := by
    intro a b
    obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
    obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
    let i := Classical.arbitrary M
    calc
      homotopyGroupCongrEquiv x e
          (HomotopyGroup.mk p * HomotopyGroup.mk q) =
        HomotopyGroup.mk
          (GenLoop.congr x e (GenLoop.transAt i q p)) := by
            rw [HomotopyGroup.mul_mk i p q]
            rfl
      _ = HomotopyGroup.mk
          (GenLoop.transAt (e i)
            (GenLoop.congr x e q) (GenLoop.congr x e p)) :=
        congrArg HomotopyGroup.mk (congr_transAt e i p q)
      _ = HomotopyGroup.mk
          (GenLoop.transAt (Classical.arbitrary N)
            (GenLoop.congr x e q) (GenLoop.congr x e p)) :=
        HomotopyGroup.transAt_indep (Classical.arbitrary N)
          (GenLoop.congr x e q) (GenLoop.congr x e p)
      _ = homotopyGroupCongrEquiv x e (HomotopyGroup.mk p) *
          homotopyGroupCongrEquiv x e (HomotopyGroup.mk q) := by
        change _ = HomotopyGroup.mk (GenLoop.congr x e p) *
          HomotopyGroup.mk (GenLoop.congr x e q)
        rw [HomotopyGroup.mul_mk (Classical.arbitrary N)]

end HomotopyGroup

end

end

public noncomputable section

set_option autoImplicit false

open scoped unitInterval Topology Topology.Homotopy

universe u v

namespace HomotopyGroup

/-- The multiplicative loop-space shift from the positive homotopy groups of
the loop space to the next homotopy groups of the original space. -/
def loopShiftMulEquiv
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x) ≃*
      HomotopyGroup.Pi (n + 2) X x :=
  (finOneMapMulEquiv n X x).trans
    ((homotopyGroupFlattenMulEquiv (Fin (n + 1)) (Fin 1) X x).trans
      (homotopyGroupCongrMulEquiv
        (Fin (n + 1) ⊕ Fin 1) (Fin (n + 2)) X x finSumFinEquiv))

/-- The loop-space shift is natural for strict postcomposition maps. -/
theorem loopShiftMulEquiv_naturality
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (x : X)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    loopShiftMulEquiv n Y (f x)
        (mapHomOfEq (ContinuousMap.strictLoopMap f x)
          (ContinuousMap.strictLoopMap_refl f x) n a) =
      HomotopyGroup.map f (loopShiftMulEquiv n X x a) := by
  have mapHomOfEq_mk
      {A : Type u} {B : Type v}
      [TopologicalSpace A] [TopologicalSpace B]
      {a₀ : A} {b₀ : B} (g : C(A, B)) (hg : g a₀ = b₀)
      (r : GenLoop (Fin (n + 1)) A a₀) :
      mapHomOfEq g hg n (HomotopyGroup.mk r) =
        HomotopyGroup.mk
          (⟨(GenLoop.map g r).1,
            fun t ht => (GenLoop.boundary (GenLoop.map g r) t ht).trans hg⟩ :
            GenLoop (Fin (n + 1)) B b₀) := by
    subst b₀
    rfl
  have mapHomOfEq_mkX
      {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
      {a₀ : A} {b₀ : B} (g : C(A, B)) (hg : g a₀ = b₀)
      (r : GenLoop (Fin (n + 1)) A a₀) :
      mapHomOfEq g hg n (HomotopyGroup.mk r) =
        HomotopyGroup.mk
          (⟨(GenLoop.map g r).1,
            fun t ht => (GenLoop.boundary (GenLoop.map g r) t ht).trans hg⟩ :
            GenLoop (Fin (n + 1)) B b₀) := by
    subst b₀
    rfl
  have mapHomOfEq_mkY
      {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
      {a₀ : A} {b₀ : B} (g : C(A, B)) (hg : g a₀ = b₀)
      (r : GenLoop (Fin (n + 1)) A a₀) :
      mapHomOfEq g hg n (HomotopyGroup.mk r) =
        HomotopyGroup.mk
          (⟨(GenLoop.map g r).1,
            fun t ht => (GenLoop.boundary (GenLoop.map g r) t ht).trans hg⟩ :
            GenLoop (Fin (n + 1)) B b₀) := by
    subst b₀
    rfl
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  let s := ContinuousMap.strictLoopMap f x
  let hs : s (Path.refl x) = Path.refl (f x) :=
    ContinuousMap.strictLoopMap_refl f x
  let pY : GenLoop (Fin (n + 1)) (LoopSpace Y (f x)) (Path.refl (f x)) :=
    ⟨(GenLoop.map s p).1,
      fun t ht => (GenLoop.boundary (GenLoop.map s p) t ht).trans hs⟩
  have strict_normalize :
      mapHomOfEq s hs n (HomotopyGroup.mk p) =
        HomotopyGroup.mk pY :=
    mapHomOfEq_mk s hs p
  rw [strict_normalize]
  let eX := GenLoop.finOneHomeomorphLoopSpace X x
  let eY := GenLoop.finOneHomeomorphLoopSpace Y (f x)
  let eiX : C(LoopSpace X x, GenLoop (Fin 1) X x) :=
    ⟨eX.symm, eX.continuous_invFun⟩
  let eiY : C(LoopSpace Y (f x), GenLoop (Fin 1) Y (f x)) :=
    ⟨eY.symm, eY.continuous_invFun⟩
  have hiX : eiX (Path.refl x) = GenLoop.const := by
    apply GenLoop.ext
    intro t
    rfl
  have hiY : eiY (Path.refl (f x)) = GenLoop.const := by
    apply GenLoop.ext
    intro t
    rfl
  let rX :
      GenLoop (Fin (n + 1)) (GenLoop (Fin 1) X x) GenLoop.const :=
    ⟨(GenLoop.map eiX p).1,
      fun t ht => (GenLoop.boundary (GenLoop.map eiX p) t ht).trans hiX⟩
  let rY :
      GenLoop (Fin (n + 1)) (GenLoop (Fin 1) Y (f x)) GenLoop.const :=
    ⟨(GenLoop.map eiY pY).1,
      fun t ht => (GenLoop.boundary (GenLoop.map eiY pY) t ht).trans hiY⟩
  have firstX :
      finOneMapMulEquiv n X x (HomotopyGroup.mk p) =
        HomotopyGroup.mk rX := by
    change mapHomOfEq eiX hiX n (HomotopyGroup.mk p) =
      HomotopyGroup.mk rX
    exact mapHomOfEq_mkX eiX hiX p
  have firstY :
      finOneMapMulEquiv n Y (f x) (HomotopyGroup.mk pY) =
        HomotopyGroup.mk rY := by
    change mapHomOfEq eiY hiY n (HomotopyGroup.mk pY) =
      HomotopyGroup.mk rY
    exact mapHomOfEq_mkY eiY hiY pY
  change
    homotopyGroupCongrMulEquiv
        (Fin (n + 1) ⊕ Fin 1) (Fin (n + 2)) Y (f x) finSumFinEquiv
      (homotopyGroupFlattenMulEquiv (Fin (n + 1)) (Fin 1) Y (f x)
        (finOneMapMulEquiv n Y (f x) (HomotopyGroup.mk pY))) =
      HomotopyGroup.map f
        (homotopyGroupCongrMulEquiv
            (Fin (n + 1) ⊕ Fin 1) (Fin (n + 2)) X x finSumFinEquiv
          (homotopyGroupFlattenMulEquiv (Fin (n + 1)) (Fin 1) X x
            (finOneMapMulEquiv n X x (HomotopyGroup.mk p))))
  rw [firstY, firstX]
  change
    HomotopyGroup.mk
        (GenLoop.congr (f x) finSumFinEquiv
          (GenLoop.genLoopGenLoopEquiv (f x) rY)) =
      HomotopyGroup.map f
        (HomotopyGroup.mk
          (GenLoop.congr x finSumFinEquiv
            (GenLoop.genLoopGenLoopEquiv x rX)))
  rw [HomotopyGroup.map_mk]
  apply congrArg HomotopyGroup.mk
  apply GenLoop.ext
  intro t
  rfl

end HomotopyGroup

/-! ## The original whole cube behind the loop shift -/

@[expose] public section

universe w

namespace GenLoop

/-- Uncurry an actual based-loop family with its original clock as the final summand. -/
def loopSpaceUncurry {M : Type w} {X : Type u} [TopologicalSpace X] {x : X}
    (alpha : GenLoop M (LoopSpace X x) (Path.refl x)) : GenLoop (M ⊕ Fin 1) X x := by
  let e := finOneHomeomorphLoopSpace X x
  let f : C(LoopSpace X x, GenLoop (Fin 1) X x) := ⟨e.symm, e.symm.continuous⟩
  have hf : f (Path.refl x) = GenLoop.const := by
    apply GenLoop.ext
    intro t
    rfl
  let p : GenLoop M (GenLoop (Fin 1) X x) GenLoop.const :=
    ⟨(GenLoop.map f alpha).1,
      fun t ht => (GenLoop.boundary (GenLoop.map f alpha) t ht).trans hf⟩
  exact GenLoop.genLoopGenLoopEquiv x p

/-- Every original family parameter and ordinary path time is read without a new clock. -/
theorem loopSpaceUncurry_apply {M : Type w} {X : Type u} [TopologicalSpace X] {x : X}
    (alpha : GenLoop M (LoopSpace X x) (Path.refl x)) (t : I^(M ⊕ Fin 1)) :
    loopSpaceUncurry alpha t = alpha (t ∘ Sum.inl) (t (Sum.inr 0)) := rfl

end GenLoop

namespace HomotopyGroup

private theorem originalLoopShiftMkComputed (n : ℕ) (X : Type u)
    [TopologicalSpace X] (x : X)
    (alpha : GenLoop (Fin (n + 1)) (LoopSpace X x) (Path.refl x)) :
    loopShiftMulEquiv n X x (HomotopyGroup.mk alpha) =
      HomotopyGroup.mk (GenLoop.congr x finSumFinEquiv (GenLoop.loopSpaceUncurry alpha)) := rfl

/-- The actual old loop shift is the complete original cube with its final loop coordinate. -/
theorem loopShiftMulEquiv_mk (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (alpha : GenLoop (Fin (n + 1)) (LoopSpace X x) (Path.refl x)) :
    loopShiftMulEquiv n X x (HomotopyGroup.mk alpha) =
      HomotopyGroup.mk (GenLoop.congr x finSumFinEquiv (GenLoop.loopSpaceUncurry alpha)) :=
  originalLoopShiftMkComputed n X x alpha

end HomotopyGroup
