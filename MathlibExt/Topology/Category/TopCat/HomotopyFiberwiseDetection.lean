/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroupUnit

/-!
# Point-fiber detection of weak homotopy equivalences

The simplicial exact-sequence argument treats positive homotopy groups and
components separately. The TopCat interface retains the actual strict-fiber
map between fibrations over one base. Standard model-category factorizations
give its actual homotopy-fiber specialization for arbitrary projections.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

universe u

namespace SSet

private theorem fibrationSequence_fiberIncl_point (S : FibrationSequence.{u}) :
    S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e := by
  rfl

private theorem piGroup_mulOne_unit {X : SSet.{u}} [KanComplex X]
    {x : X _⦋0⦌} {n : ℕ} :
    (KanComplex.π.group (X := X) (x := x) (n := n)).toMulOneClass.one =
      (KanComplex.π.instOne (X := X) (x := x) (n := n + 1)).one := by
  change (KanComplex.π.group (X := X) (x := x) (n := n)).one = _
  exact KanComplex.π.group_one_eq_instOne

private theorem piGroup_division_unit {X : SSet.{u}} [KanComplex X]
    {x : X _⦋0⦌} {n : ℕ} :
    (inferInstance : DivisionMonoid (KanComplex.π (n + 1) X x)).one =
      (KanComplex.π.instOne (X := X) (x := x) (n := n + 1)).one := by
  change (KanComplex.π.group (X := X) (x := x) (n := n)).one = _
  exact KanComplex.π.group_one_eq_instOne

private theorem piMap_congr
    {X Y : SSet.{u}} (f g : X ⟶ Y) (hfg : f = g)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hf : f.app _ x = y) (hg : g.app _ x = y)
    (n : ℕ) (a : KanComplex.π n X x) :
    KanComplex.π.map f hf n a = KanComplex.π.map g hg n a := by
  cases hfg
  rfl

private theorem fibrationSequenceHom_total_base
    {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T) (n : ℕ)
    (a : KanComplex.π n S.E S.e) :
    KanComplex.π.map T.p T.hb n (KanComplex.π.map f.totalMap f.total_pt n a) =
      KanComplex.π.map f.baseMap f.base_pt n (KanComplex.π.map S.p S.hb n a) := by
  have ht : (f.totalMap ≫ T.p).app _ S.e = T.b := by
    change T.p.app _ (f.totalMap.app _ S.e) = T.b
    rw [f.total_pt, T.hb]
  have hs : (S.p ≫ f.baseMap).app _ S.e = T.b := by
    change f.baseMap.app _ (S.p.app _ S.e) = T.b
    rw [S.hb, f.base_pt]
  rw [← KanComplex.π.map_comp_apply f.totalMap T.p f.total_pt T.hb ht,
    ← KanComplex.π.map_comp_apply S.p f.baseMap S.hb f.base_pt hs]
  exact piMap_congr _ _ f.comm ht hs n a

private theorem fibrationSequenceHom_total_fiber
    {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T) (n : ℕ)
    (a : KanComplex.π n S.fiber S.fiberPoint) :
    KanComplex.π.map f.totalMap f.total_pt n
        (KanComplex.π.map S.fiberIncl (fibrationSequence_fiberIncl_point S) n a) =
      KanComplex.π.map T.fiberIncl (fibrationSequence_fiberIncl_point T) n
        (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n a) := by
  have hs : (S.fiberIncl ≫ f.totalMap).app _ S.fiberPoint = T.e := by
    change f.totalMap.app _ S.e = T.e
    exact f.total_pt
  have ht : (f.fiberMap ≫ T.fiberIncl).app _ S.fiberPoint = T.e := by
    change T.fiberIncl.app _ (f.fiberMap.app _ S.fiberPoint) = T.e
    rw [f.fiberMap_app_basePoint]
    rfl
  rw [← KanComplex.π.map_comp_apply S.fiberIncl f.totalMap
      (fibrationSequence_fiberIncl_point S) f.total_pt hs,
    ← KanComplex.π.map_comp_apply f.fiberMap T.fiberIncl
      f.fiberMap_app_basePoint (fibrationSequence_fiberIncl_point T) ht]
  exact piMap_congr _ _ f.fiberMap_ι.symm hs ht n a

private theorem fibrationSequenceHom_detects_unit
    {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T) (n : ℕ)
    (hBinj : Function.Injective (KanComplex.π.map f.baseMap f.base_pt n))
    (hBsurj : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hFinj : Function.Injective
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n))
    (a : KanComplex.π n S.E S.e)
    (ha : KanComplex.π.map f.totalMap f.total_pt n a = 1) : a = 1 := by
  have hpa : KanComplex.π.map S.p S.hb n a = 1 := by
    apply hBinj
    rw [← fibrationSequenceHom_total_base, ha, KanComplex.π.map_one,
      KanComplex.π.map_one]
  obtain ⟨c, hcRaw⟩ := S.exactness_at_E a hpa
  have hc : KanComplex.π.map S.fiberIncl (fibrationSequence_fiberIncl_point S) n c = a :=
    hcRaw
  have htc : KanComplex.π.map T.fiberIncl (fibrationSequence_fiberIncl_point T) n
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n c) = 1 := by
    rw [← fibrationSequenceHom_total_fiber, hc, ha]
  obtain ⟨b, hb⟩ := T.exactness_at_fiber
    (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n c) htc
  obtain ⟨b', hb'⟩ := hBsurj b
  have hδ : S.connectingMap (n := n) b' = c := by
    apply hFinj
    rw [FibrationSequence.connectingMap_naturality f, hb', hb]
  rw [← hc, ← hδ]
  exact S.fiberIncl_map_connectingMap_eq_one b'

private theorem piMap_inv
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (h : f.app _ x = y)
    (n : ℕ) (a : KanComplex.π (n + 1) X x) :
    KanComplex.π.map f h (n + 1) a⁻¹ = (KanComplex.π.map f h (n + 1) a)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  rw [← KanComplex.π.map_mul, inv_mul_cancel]
  change KanComplex.π.map f h (n + 1)
      (KanComplex.π.group (X := X) (x := x) (n := n)).toMulOneClass.one =
    (inferInstance : DivisionMonoid (KanComplex.π (n + 1) Y y)).one
  rw [piGroup_mulOne_unit, piGroup_division_unit]
  exact KanComplex.π.map_one f h (n + 1)

private theorem fibrationSequenceHom_positive_surjective
    {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T) (n : ℕ)
    (hBsurj : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hFinj : Function.Injective
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n))
    (hFsurj : Function.Surjective
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint (n + 1))) :
    Function.Surjective (KanComplex.π.map f.totalMap f.total_pt (n + 1)) := by
  intro a
  obtain ⟨b, hb⟩ := hBsurj (KanComplex.π.map T.p T.hb (n + 1) a)
  have hδ : S.connectingMap (n := n) b = 1 := by
    apply hFinj
    rw [FibrationSequence.connectingMap_naturality f, hb,
      T.connectingMap_map_eq_one, KanComplex.π.map_one]
  obtain ⟨c, hc⟩ := S.exactness_at_B b hδ
  let d := a * (KanComplex.π.map f.totalMap f.total_pt (n + 1) c)⁻¹
  have hd : KanComplex.π.map T.p T.hb (n + 1) d = 1 := by
    dsimp only [d]
    rw [KanComplex.π.map_mul, piMap_inv, fibrationSequenceHom_total_base, hc, hb,
      mul_inv_cancel]
    change (KanComplex.π.group (X := T.B) (x := T.b) (n := n)).one =
      (KanComplex.π.instOne (X := T.B) (x := T.b) (n := n + 1)).one
    exact KanComplex.π.group_one_eq_instOne
  obtain ⟨d', hd'Raw⟩ := T.exactness_at_E d hd
  have hd' : KanComplex.π.map T.fiberIncl
      (fibrationSequence_fiberIncl_point T) (n + 1) d' = d := hd'Raw
  obtain ⟨d'', hd''⟩ := hFsurj d'
  refine ⟨KanComplex.π.map S.fiberIncl
    (fibrationSequence_fiberIncl_point S) (n + 1) d'' * c, ?_⟩
  rw [KanComplex.π.map_mul, fibrationSequenceHom_total_fiber, hd'', hd']
  dsimp only [d]
  rw [mul_assoc, inv_mul_cancel, mul_one]

private theorem fibrationSequenceHom_positive_injective
    {S T : FibrationSequence.{u}} (f : FibrationSequenceHom S T) (n : ℕ)
    (hBinj : Function.Injective (KanComplex.π.map f.baseMap f.base_pt (n + 1)))
    (hBsurj : Function.Surjective (KanComplex.π.map f.baseMap f.base_pt (n + 2)))
    (hFinj : Function.Injective
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint (n + 1))) :
    Function.Injective (KanComplex.π.map f.totalMap f.total_pt (n + 1)) := by
  intro a b hab
  have hunit : KanComplex.π.map f.totalMap f.total_pt (n + 1) (a * b⁻¹) = 1 := by
    rw [KanComplex.π.map_mul, piMap_inv, hab, mul_inv_cancel]
    change (KanComplex.π.group (X := T.E) (x := T.e) (n := n)).one =
      (KanComplex.π.instOne (X := T.E) (x := T.e) (n := n + 1)).one
    exact KanComplex.π.group_one_eq_instOne
  have h := fibrationSequenceHom_detects_unit f (n + 1) hBinj hBsurj hFinj
    (a * b⁻¹) (by
      simpa only [KanComplex.π.group_one_eq_instOne, piGroup_mulOne_unit,
        piGroup_division_unit] using hunit)
  apply (mul_inv_eq_one).mp
  change a * b⁻¹ = (inferInstance : DivisionMonoid (KanComplex.π (n + 1) S.E S.e)).one
  rw [piGroup_division_unit]
  exact h

private theorem piZeroEquiv_self {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    KanComplex.π₀EquivπZero x (π₀.mk x) = 1 := by
  rw [KanComplex.π₀EquivπZero_mk]
  change KanComplex.π.mk ((PtSimplex.equiv₀ x).symm x) =
    KanComplex.π.mk (RelativeMorphism.const : X.PtSimplex 0 x)
  congr 1
  apply (PtSimplex.equiv₀ x).injective
  rw [Equiv.apply_symm_apply]
  simp only [PtSimplex.equiv₀_apply, RelativeMorphism.const_map, yonedaEquiv_const]

private theorem mapPiZero_injective_of_detects_unit
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    (hunit : ∀ (x : X _⦋0⦌) (a : KanComplex.π 0 X x),
      KanComplex.π.map f rfl 0 a = 1 → a = 1) :
    Function.Injective (mapπ₀ f) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := a.mk_surjective
  obtain ⟨y, rfl⟩ := b.mk_surjective
  let c := KanComplex.π₀EquivπZero x (π₀.mk y)
  have hc : KanComplex.π.map f rfl 0 c = 1 := by
    have hn := congrFun
      (KanComplex.mapπ_comp_π₀EquivπZero f x (f.app _ x) rfl) (π₀.mk y)
    have hr : KanComplex.π₀EquivπZero (f.app _ x) (mapπ₀ f (π₀.mk y)) = 1 := by
      rw [← hab, mapπ₀_mk, piZeroEquiv_self]
    exact hn.trans hr
  apply (KanComplex.π₀EquivπZero x).injective
  exact (piZeroEquiv_self x).trans (hunit x c hc).symm

private theorem W_bijective_piMap_at_point
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : KanComplex.W f)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) (n : ℕ) :
    Function.Bijective (KanComplex.π.map f h n) := by
  cases h
  exact hf.bijective_piMap n x

private abbrev sourceFibrationSequence
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex B]
    (e : E _⦋0⦌) : FibrationSequence.{u} where
  E := E
  B := B
  p := p
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := e
  b := p.app _ e
  hb := rfl

private abbrev targetFibrationSequence
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p) (e : E _⦋0⦌) : FibrationSequence.{u} where
  E := E'
  B := B
  p := q
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := s.app _ e
  b := p.app _ e
  hb := congrArg (fun k => k.app (op ⦋0⦌) e) comm

private abbrev sameBaseFibrationSequenceHom
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p) (e : E _⦋0⦌) :
    FibrationSequenceHom (sourceFibrationSequence p e)
      (targetFibrationSequence p q s comm e) where
  totalMap := s
  baseMap := 𝟙 B
  comm := by simpa using comm
  total_pt := rfl
  base_pt := rfl

private abbrev sameBaseSimplicialFiberMap
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (s : E ⟶ E') (comm : s ≫ q = p) (b : B _⦋0⦌) :
    (Subcomplex.fiber p b : SSet.{u}) ⟶ (Subcomplex.fiber q b : SSet.{u}) :=
  Subcomplex.mapFiber s (𝟙 B) (by simpa using comm) rfl

private theorem sameBaseFibrationSequenceHom_fiberMap
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p) (e : E _⦋0⦌) :
    (sameBaseFibrationSequenceHom p q s comm e).fiberMap =
      sameBaseSimplicialFiberMap p q s comm (p.app _ e) := by
  rfl

private theorem sameBase_total_detects_unit
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B _⦋0⦌, KanComplex.W (sameBaseSimplicialFiberMap p q s comm b))
    (n : ℕ) (e : E _⦋0⦌) (a : KanComplex.π n E e)
    (ha : KanComplex.π.map s rfl n a = 1) : a = 1 := by
  let f := sameBaseFibrationSequenceHom p q s comm e
  have hf : KanComplex.W f.fiberMap := by
    rw [sameBaseFibrationSequenceHom_fiberMap]
    exact hF _
  apply fibrationSequenceHom_detects_unit f n
  · intro a b h
    change KanComplex.π.map (𝟙 B) (x := p.app _ e) (y := p.app _ e) rfl n a =
      KanComplex.π.map (𝟙 B) (x := p.app _ e) (y := p.app _ e) rfl n b at h
    simpa only [KanComplex.π.map_id_apply] using h
  · intro b
    refine ⟨b, ?_⟩
    exact KanComplex.π.map_id_apply b
  · exact (W_bijective_piMap_at_point hf f.fiberMap_app_basePoint n).1
  · exact ha

private theorem sameBase_total_positive_bijective
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B _⦋0⦌, KanComplex.W (sameBaseSimplicialFiberMap p q s comm b))
    (n : ℕ) (e : E _⦋0⦌) :
    Function.Bijective (KanComplex.π.map s rfl (n + 1) (x := e)) := by
  let f := sameBaseFibrationSequenceHom p q s comm e
  have hf : KanComplex.W f.fiberMap := by
    rw [sameBaseFibrationSequenceHom_fiberMap]
    exact hF _
  have hB (m : ℕ) : Function.Bijective
      (KanComplex.π.map f.baseMap f.base_pt m) := by
    constructor
    · intro a b h
      change KanComplex.π.map (𝟙 B) (x := p.app _ e) (y := p.app _ e) rfl m a =
        KanComplex.π.map (𝟙 B) (x := p.app _ e) (y := p.app _ e) rfl m b at h
      simpa only [KanComplex.π.map_id_apply] using h
    · intro b
      exact ⟨b, KanComplex.π.map_id_apply b⟩
  have hFi (m : ℕ) : Function.Bijective
      (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint m) :=
    W_bijective_piMap_at_point hf f.fiberMap_app_basePoint m
  exact ⟨fibrationSequenceHom_positive_injective f n (hB _).1 (hB _).2 (hFi _).1,
    fibrationSequenceHom_positive_surjective f n (hB _).2 (hFi _).1 (hFi _).2⟩

private theorem sameBase_mapPiZero_surjective
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B _⦋0⦌, KanComplex.W (sameBaseSimplicialFiberMap p q s comm b)) :
    Function.Surjective (mapπ₀ s) := by
  intro a
  obtain ⟨y, rfl⟩ := a.mk_surjective
  let b := q.app (op ⦋0⦌) y
  let y' : (Subcomplex.fiber q b : SSet.{u}) _⦋0⦌ :=
    Subcomplex.fiber.basePoint y rfl
  obtain ⟨c, hc⟩ := (hF b).bijective_mapπ₀.2 (π₀.mk y')
  obtain ⟨x, rfl⟩ := c.mk_surjective
  refine ⟨π₀.mk x.val, ?_⟩
  have h := congrArg (mapπ₀ (Subcomplex.fiber q b).ι) hc
  simp only [mapπ₀_mk] at h
  change π₀.mk (s.app _ x.val) = π₀.mk y at h
  exact h

private theorem sameBase_simplicial_mem_W_of_fiber_maps
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] [KanComplex B]
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B _⦋0⦌, KanComplex.W (sameBaseSimplicialFiberMap p q s comm b)) :
    KanComplex.W s := by
  let _ : KanComplex E := isFibrant_of_fibration p
  let _ : KanComplex E' := isFibrant_of_fibration q
  apply (KanComplex.W_iff s).mpr
  refine ⟨⟨?_, sameBase_mapPiZero_surjective p q s comm hF⟩, ?_⟩
  · exact mapPiZero_injective_of_detects_unit s
      (fun e a ha => sameBase_total_detects_unit p q s comm hF 0 e a ha)
  · exact sameBase_total_positive_bijective p q s comm hF

end SSet

namespace TopCat

private theorem singular_map_fibration {E B : TopCat.{u}}
    (p : E ⟶ B) [Fibration p] : Fibration (TopCat.toSSet.map p) := by
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := sSetTopAdj) _
    ((HomotopicalAlgebra.fibration_iff p).mp inferInstance)

private def singularPointIso :
    TopCat.toSSet.obj (TopCat.of PUnit) ≅ (Δ[0] : SSet.{u}) :=
  (TopCat.isTerminalPUnit.isTerminalObj TopCat.toSSet).uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀

private theorem singularPointFiber_isPullback {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) :
    IsPullback
      (TopCat.toSSet.map (pullback.fst p (TopCat.const (X := TopCat.of PUnit) b)))
      (TopCat.toSSet.map (pullback.snd p (TopCat.const (X := TopCat.of PUnit) b)) ≫
        singularPointIso.hom)
      (TopCat.toSSet.map p) (SSet.const (X := Δ[0]) (TopCat.toSSetObj₀Equiv.symm b)) := by
  let c : TopCat.of PUnit ⟶ B := TopCat.const b
  have hbottom : TopCat.toSSet.map c =
      singularPointIso.hom ≫ SSet.const (X := Δ[0]) (TopCat.toSSetObj₀Equiv.symm b) := by
    rw [SSet.comp_const]
    exact TopCat.toSSet_map_const _ b
  have sq := (IsPullback.of_hasPullback p c).map TopCat.toSSet
  have right : IsPullback singularPointIso.hom (TopCat.toSSet.map c)
      (SSet.const (X := Δ[0]) (TopCat.toSSetObj₀Equiv.symm b))
      (𝟙 (TopCat.toSSet.obj B)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hbottom]⟩
  have h := sq.flip.paste_horiz right
  simpa only [Category.comp_id] using h.flip

private def singularStrictFiberIso {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    TopCat.toSSet.obj (pullback p (TopCat.const (X := TopCat.of PUnit) b)) ≅
      (SSet.Subcomplex.fiber (TopCat.toSSet.map p)
        (TopCat.toSSetObj₀Equiv.symm b) : SSet.{u}) :=
  (singularPointFiber_isPullback p b).isoIsPullback _ _
    (SSet.Subcomplex.fiber_isPullback _ _)

private theorem singularStrictFiberIso_hom_ι {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) :
    (singularStrictFiberIso p b).hom ≫
        (SSet.Subcomplex.fiber (TopCat.toSSet.map p)
          (TopCat.toSSetObj₀Equiv.symm b)).ι =
      TopCat.toSSet.map (pullback.fst p (TopCat.const (X := TopCat.of PUnit) b)) :=
  (singularPointFiber_isPullback p b).isoIsPullback_hom_fst _ _
    (SSet.Subcomplex.fiber_isPullback _ _)

private theorem singularStrictFiberMap_naturality {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p) (b : B) :
    (singularStrictFiberIso p b).hom ≫
        SSet.sameBaseSimplicialFiberMap (TopCat.toSSet.map p) (TopCat.toSSet.map q)
          (TopCat.toSSet.map s) (by rw [← Functor.map_comp, comm])
          (TopCat.toSSetObj₀Equiv.symm b) =
      TopCat.toSSet.map (strictFiberMapOfSquare (p := p) (q := q) s (𝟙 B)
        (by simpa using comm.symm) b) ≫ (singularStrictFiberIso q b).hom := by
  let τ : pullback p (TopCat.const (X := TopCat.of PUnit) b) ⟶
      pullback q (TopCat.const (X := TopCat.of PUnit) b) :=
    strictFiberMapOfSquare (p := p) (q := q) s (𝟙 B) (by simpa using comm.symm) b
  change (singularStrictFiberIso p b).hom ≫
      SSet.sameBaseSimplicialFiberMap (TopCat.toSSet.map p) (TopCat.toSSet.map q)
        (TopCat.toSSet.map s) (by rw [← Functor.map_comp, comm])
        (TopCat.toSSetObj₀Equiv.symm b) =
    TopCat.toSSet.map τ ≫ (singularStrictFiberIso q b).hom
  apply (cancel_mono (SSet.Subcomplex.fiber (TopCat.toSSet.map q)
    (TopCat.toSSetObj₀Equiv.symm b)).ι).mp
  rw [Category.assoc, SSet.Subcomplex.mapFiber_ι, ← Category.assoc,
    singularStrictFiberIso_hom_ι]
  rw [Category.assoc, singularStrictFiberIso_hom_ι]
  have ht : τ ≫ pullback.fst q (TopCat.const (X := TopCat.of PUnit) b) =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) ≫ s :=
    strictFiberMapOfSquare_fst (p := p) (q := q) s (𝟙 B)
      (by simpa using comm.symm) b
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg TopCat.toSSet.map ht.symm

/-- A map between actual fibrations over one base is weak if its actual
strict-fiber map is weak over every base point. This includes components and
all positive homotopy groups, and requires no CW hypothesis. -/
theorem mem_weakHomotopyEquivalences_of_strictFiberMaps
    {E E' B : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [Fibration p] [Fibration q] (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B, weakHomotopyEquivalences
      (strictFiberMapOfSquare (p := p) (q := q) s (𝟙 B)
        (by simpa using comm.symm) b)) :
    weakHomotopyEquivalences s := by
  let _ : Fibration (TopCat.toSSet.map p) := singular_map_fibration p
  let _ : Fibration (TopCat.toSSet.map q) := singular_map_fibration q
  let _ : SSet.KanComplex (TopCat.toSSet.obj B) := TopCat.toSSet_obj_kanComplex B
  apply (TopCat.mem_weakHomotopyEquivalences_iff s).mpr
  apply SSet.sameBase_simplicial_mem_W_of_fiber_maps
    (TopCat.toSSet.map p) (TopCat.toSSet.map q) (TopCat.toSSet.map s)
    (by rw [← Functor.map_comp, comm])
  intro b₀
  obtain ⟨b, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective b₀
  let eP := singularStrictFiberIso p b
  let eQ := singularStrictFiberIso q b
  let τ : pullback p (TopCat.const (X := TopCat.of PUnit) b) ⟶
      pullback q (TopCat.const (X := TopCat.of PUnit) b) :=
    strictFiberMapOfSquare (p := p) (q := q) s (𝟙 B) (by simpa using comm.symm) b
  let _ : SSet.KanComplex (TopCat.toSSet.obj
      (pullback p (TopCat.const (X := TopCat.of PUnit) b))) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj
      (pullback q (TopCat.const (X := TopCat.of PUnit) b))) :=
    TopCat.toSSet_obj_kanComplex _
  have hmap : SSet.KanComplex.W (TopCat.toSSet.map τ) :=
    (TopCat.mem_weakHomotopyEquivalences_iff _).mp (hF b)
  have hInv : SSet.KanComplex.W eP.inv := SSet.KanComplex.W.ofIso eP.symm
  have hweak : SSet.KanComplex.W (eP.inv ≫ TopCat.toSSet.map τ ≫ eQ.hom) :=
    SSet.KanComplex.W.comp hInv
      (SSet.KanComplex.W.comp hmap (SSet.KanComplex.W.ofIso eQ))
  have hnat : eP.hom ≫
      SSet.sameBaseSimplicialFiberMap (TopCat.toSSet.map p) (TopCat.toSSet.map q)
        (TopCat.toSSet.map s) (by rw [← Functor.map_comp, comm])
        (TopCat.toSSetObj₀Equiv.symm b) = TopCat.toSSet.map τ ≫ eQ.hom :=
    singularStrictFiberMap_naturality p q s comm b
  have hfac : eP.inv ≫ TopCat.toSSet.map τ ≫ eQ.hom =
        SSet.sameBaseSimplicialFiberMap (TopCat.toSSet.map p) (TopCat.toSSet.map q)
          (TopCat.toSSet.map s) (by rw [← Functor.map_comp, comm])
          (TopCat.toSSetObj₀Equiv.symm b) := by
    rw [← hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hfac] at hweak
  exact hweak

private def sameBaseHomotopyFiberMap {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p) (b : B) :
    homotopyFiber p b ⟶ homotopyFiber q b :=
  homotopyFiberMapOfSquare (p := p) (q := q) s (𝟙 B) (by simpa using comm.symm) b

private theorem sameBaseHomotopyFiberMap_total {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p) (b : B) :
    sameBaseHomotopyFiberMap p q s comm b ≫ homotopyFiberToTotal q b =
      homotopyFiberToTotal p b ≫ s :=
  homotopyFiberMapOfSquare_toTotal (p := p) (q := q) s (𝟙 B)
    (by simpa using comm.symm) b

private theorem sameBaseHomotopyFiberMap_path {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p) (b : B) :
    sameBaseHomotopyFiberMap p q s comm b ≫ homotopyFiberPath q b =
      homotopyFiberPath p b := by
  have h : sameBaseHomotopyFiberMap p q s comm b ≫ homotopyFiberPath q b =
      homotopyFiberPath p b ≫ pathObjectMap (𝟙 B) :=
    homotopyFiberMapOfSquare_path (p := p) (q := q) s (𝟙 B)
      (by simpa using comm.symm) b
  simpa only [pathObjectMap_id, Category.comp_id] using h

private theorem sameBaseHomotopyFiberMap_congr {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s t : E ⟶ E') (hst : s = t)
    (hs : s ≫ q = p) (ht : t ≫ q = p) (b : B) :
    sameBaseHomotopyFiberMap p q s hs b = sameBaseHomotopyFiberMap p q t ht b := by
  cases hst
  rfl

private theorem sameBaseHomotopyFiberMap_comp {E E' E'' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (r : E'' ⟶ B)
    (s : E ⟶ E') (t : E' ⟶ E'') (hs : s ≫ q = p) (ht : t ≫ r = q) (b : B) :
    sameBaseHomotopyFiberMap p q s hs b ≫ sameBaseHomotopyFiberMap q r t ht b =
      sameBaseHomotopyFiberMap p r (s ≫ t) (by rw [Category.assoc, ht, hs]) b := by
  apply homotopyPullback_hom_ext
  · change (sameBaseHomotopyFiberMap p q s hs b ≫
        sameBaseHomotopyFiberMap q r t ht b) ≫ homotopyFiberToTotal r b = _
    rw [Category.assoc, sameBaseHomotopyFiberMap_total, ← Category.assoc,
      sameBaseHomotopyFiberMap_total, Category.assoc, sameBaseHomotopyFiberMap_total]
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · change (sameBaseHomotopyFiberMap p q s hs b ≫
        sameBaseHomotopyFiberMap q r t ht b) ≫ homotopyFiberPath r b = _
    rw [Category.assoc, sameBaseHomotopyFiberMap_path, sameBaseHomotopyFiberMap_path,
      sameBaseHomotopyFiberMap_path]

private theorem sameBaseHomotopyFiberMap_mem {E E' B : TopCat.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p) (b : B)
    (hs : weakHomotopyEquivalences s) :
    weakHomotopyEquivalences (sameBaseHomotopyFiberMap p q s comm b) :=
  homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences (p := p) (q := q)
    s (𝟙 B) (by simpa using comm.symm) b hs
    (weakHomotopyEquivalences.of_isIso (𝟙 B))

/-- For arbitrary projections over one base, weakness of all actual
homotopy-fiber maps detects weakness of the given total map. The proof uses
standard factorization/lifting and retains the original map in its conclusion. -/
theorem mem_weakHomotopyEquivalences_of_homotopyFiberMaps
    {E E' B : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B) (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B, weakHomotopyEquivalences
      (homotopyFiberMapOfSquare (p := p) (q := q) s (𝟙 B)
        (by simpa using comm.symm) b)) :
    weakHomotopyEquivalences s := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let dP := MorphismProperty.factorizationData
    (trivialCofibrations TopCat.{u}) (fibrations TopCat.{u}) p
  let dQ := MorphismProperty.factorizationData
    (trivialCofibrations TopCat.{u}) (fibrations TopCat.{u}) q
  have hiP := (mem_trivialCofibrations_iff dP.i).mp dP.hi
  have hiQ := (mem_trivialCofibrations_iff dQ.i).mp dQ.hi
  let _ : Cofibration dP.i := hiP.1
  let _ : WeakEquivalence dP.i := hiP.2
  let _ : Fibration dP.p := (HomotopicalAlgebra.fibration_iff _).mpr dP.hp
  let _ : Fibration dQ.p := (HomotopicalAlgebra.fibration_iff _).mpr dQ.hp
  have hP : weakHomotopyEquivalences dP.i :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp hiP.2
  have hQ : weakHomotopyEquivalences dQ.i :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp hiQ.2
  let sq : CommSq (s ≫ dQ.i) dP.i dQ.p dP.p := ⟨by
    rw [Category.assoc, dQ.fac, comm, dP.fac]⟩
  let l := sq.lift
  have hl : weakHomotopyEquivalences l := by
    apply mem_weakHomotopyEquivalences_of_strictFiberMaps dP.p dQ.p l sq.fac_right
    intro b
    have hleft : weakHomotopyEquivalences
        (sameBaseHomotopyFiberMap p dP.p dP.i dP.fac b) :=
      sameBaseHomotopyFiberMap_mem _ _ _ _ _ hP
    have hright : weakHomotopyEquivalences
        (sameBaseHomotopyFiberMap q dQ.p dQ.i dQ.fac b) :=
      sameBaseHomotopyFiberMap_mem _ _ _ _ _ hQ
    have horiginal : weakHomotopyEquivalences (sameBaseHomotopyFiberMap p q s comm b) :=
      hF b
    have heq : sameBaseHomotopyFiberMap p dP.p dP.i dP.fac b ≫
        sameBaseHomotopyFiberMap dP.p dQ.p l sq.fac_right b =
      sameBaseHomotopyFiberMap p q s comm b ≫
        sameBaseHomotopyFiberMap q dQ.p dQ.i dQ.fac b := by
      rw [sameBaseHomotopyFiberMap_comp, sameBaseHomotopyFiberMap_comp]
      exact sameBaseHomotopyFiberMap_congr _ _ _ _ sq.fac_left _ _ b
    have hcomp : weakHomotopyEquivalences
        (sameBaseHomotopyFiberMap p dP.p dP.i dP.fac b ≫
          sameBaseHomotopyFiberMap dP.p dQ.p l sq.fac_right b) := by
      rw [heq]
      exact weakHomotopyEquivalences.comp_mem _ _ horiginal hright
    have hfiber : weakHomotopyEquivalences
        (sameBaseHomotopyFiberMap dP.p dQ.p l sq.fac_right b) :=
      weakHomotopyEquivalences.of_precomp _ _ hleft hcomp
    let sigma : pullback dP.p (TopCat.const (X := TopCat.of PUnit) b) ⟶
        pullback dQ.p (TopCat.const (X := TopCat.of PUnit) b) :=
      strictFiberMapOfSquare (p := dP.p) (q := dQ.p) l (𝟙 B)
        (by simpa only [Category.comp_id] using sq.fac_right.symm) b
    have hn : sigma ≫ strictFiberToHomotopyFiber dQ.p b =
        strictFiberToHomotopyFiber dP.p b ≫
          sameBaseHomotopyFiberMap dP.p dQ.p l sq.fac_right b :=
      strictFiberToHomotopyFiber_naturality (p := dP.p) (q := dQ.p) l (𝟙 B)
        (by simpa only [Category.comp_id] using sq.fac_right.symm) b
    have hsource := strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences dP.p b
    have htarget := strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences dQ.p b
    have hstrict : weakHomotopyEquivalences (sigma ≫ strictFiberToHomotopyFiber dQ.p b) := by
      rw [hn]
      exact weakHomotopyEquivalences.comp_mem _ _ hsource hfiber
    exact weakHomotopyEquivalences.of_postcomp _ _ htarget hstrict
  have hcomp : weakHomotopyEquivalences (s ≫ dQ.i) := by
    rw [← sq.fac_left]
    exact weakHomotopyEquivalences.comp_mem _ _ hP hl
  exact weakHomotopyEquivalences.of_postcomp _ _ hQ hcomp

end TopCat
