/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Universal
public import MathlibExt.CategoryTheory.Functor.Effaceable
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Effaceable δ-functors

Effacements kill a functor along a monomorphism; coeffacements do so along an
epimorphism. Positive-degree effacements extend a degree-zero map uniquely
between cohomological δ-functors. The homological construction uses
positive-degree coeffacements of the target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂


section Abelian

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

private abbrev coConnectingAt (D : CohomologicalDeltaFunctor A B) (n : ℕ)
    (Z : ShortComplex A) (hZ : Z.ShortExact) :
    (D.T n).obj Z.X₃ ⟶ (D.T (n + 1)).obj Z.X₁ :=
  (D.connecting n).app ⟨Z, hZ⟩

private abbrev hoConnectingAt (D : HomologicalDeltaFunctor A B) (n : ℕ)
    (Z : ShortComplex A) (hZ : Z.ShortExact) :
    (D.T (n + 1)).obj Z.X₃ ⟶ (D.T n).obj Z.X₁ :=
  (D.connecting n).app ⟨Z, hZ⟩

namespace CohomologicalDeltaFunctor

variable {T S : CohomologicalDeltaFunctor A B}

private theorem effaceConnecting_epi {n : ℕ} {X J : A} (j : X ⟶ J) [Mono j]
    (hkill : (T.T (n + 1)).map j = 0) :
    Epi (coConnectingAt T n (ShortComplex.cokernelSequence j)
      (ShortComplex.shortExact_cokernelSequence j)) := by
  obtain ⟨w, hex⟩ := T.exactLeft n
    ⟨ShortComplex.cokernelSequence j, ShortComplex.shortExact_cokernelSequence j⟩
  have hk : (T.T (n + 1)).map (ShortComplex.cokernelSequence j).f = 0 := by
    change (T.T (n + 1)).map j = 0
    exact hkill
  exact (ShortComplex.exact_iff_epi _ hk).mp hex

private theorem effaceDescent_condition {n : ℕ} (f : T.T n ⟶ S.T n)
    {X J : A} (j : X ⟶ J) [Mono j] :
    kernel.ι (coConnectingAt T n (ShortComplex.cokernelSequence j)
        (ShortComplex.shortExact_cokernelSequence j)) ≫
      (f.app (cokernel j) ≫ coConnectingAt S n (ShortComplex.cokernelSequence j)
        (ShortComplex.shortExact_cokernelSequence j)) = 0 := by
  let Z := ShortComplex.cokernelSequence j
  let hZ := ShortComplex.shortExact_cokernelSequence j
  let dT := coConnectingAt T n Z hZ
  let dS := coConnectingAt S n Z hZ
  obtain ⟨wT, hex⟩ := T.exactRight n ⟨Z, hZ⟩
  change (T.T n).map Z.g ≫ dT = 0 at wT
  change (ShortComplex.mk ((T.T n).map Z.g) dT wT).Exact at hex
  obtain ⟨V, ρ, hρ, l, hl⟩ :=
    ShortComplex.Exact.exact_up_to_refinements hex (kernel.ι dT) (kernel.condition dT)
  have := hρ
  change ρ ≫ kernel.ι dT = l ≫ (T.T n).map Z.g at hl
  obtain ⟨wS, -⟩ := S.exactRight n ⟨Z, hZ⟩
  change (S.T n).map Z.g ≫ dS = 0 at wS
  apply (cancel_epi ρ).mp
  change ρ ≫ (kernel.ι dT ≫ (f.app Z.X₃ ≫ dS)) = ρ ≫ 0
  calc
    ρ ≫ (kernel.ι dT ≫ (f.app Z.X₃ ≫ dS)) =
        (ρ ≫ kernel.ι dT) ≫ f.app Z.X₃ ≫ dS := by simp only [Category.assoc]
    _ = (l ≫ (T.T n).map Z.g) ≫ f.app Z.X₃ ≫ dS := by rw [hl]
    _ = l ≫ ((T.T n).map Z.g ≫ f.app Z.X₃) ≫ dS := by
      simp only [Category.assoc]
    _ = l ≫ (f.app Z.X₂ ≫ (S.T n).map Z.g) ≫ dS := by rw [f.naturality Z.g]
    _ = l ≫ f.app Z.X₂ ≫ ((S.T n).map Z.g ≫ dS) := by simp only [Category.assoc]
    _ = 0 := by rw [wS, comp_zero, comp_zero]
    _ = ρ ≫ 0 := by simp only [comp_zero]

private noncomputable def effaceDescent {n : ℕ} (f : T.T n ⟶ S.T n)
    {X J : A} (j : X ⟶ J) (hm : Mono j)
    (hkill : (T.T (n + 1)).map j = 0) :
    (T.T (n + 1)).obj X ⟶ (S.T (n + 1)).obj X := by
  letI := hm
  letI := effaceConnecting_epi (T := T) j hkill
  exact Abelian.epiDesc
    (coConnectingAt T n (ShortComplex.cokernelSequence j)
      (ShortComplex.shortExact_cokernelSequence j))
    (f.app (cokernel j) ≫
      coConnectingAt S n (ShortComplex.cokernelSequence j)
        (ShortComplex.shortExact_cokernelSequence j))
    (effaceDescent_condition (T := T) (S := S) f j)

private theorem effaceDescent_spec {n : ℕ} (f : T.T n ⟶ S.T n)
    {X J : A} (j : X ⟶ J) (hm : Mono j)
    (hkill : (T.T (n + 1)).map j = 0) :
    coConnectingAt T n (ShortComplex.cokernelSequence j)
        (letI := hm; ShortComplex.shortExact_cokernelSequence j) ≫
      effaceDescent (T := T) (S := S) f j hm hkill =
        f.app (cokernel j) ≫ coConnectingAt S n (ShortComplex.cokernelSequence j)
          (letI := hm; ShortComplex.shortExact_cokernelSequence j) := by
  unfold effaceDescent
  have := hm
  have := effaceConnecting_epi (T := T) j hkill
  exact Abelian.comp_epiDesc _ _ _

private theorem connecting_naturality (D : CohomologicalDeltaFunctor A B) (n : ℕ)
    {Z W : ShortComplex A} (φ : Z ⟶ W) (hZ : Z.ShortExact) (hW : W.ShortExact) :
    (D.T n).map φ.τ₃ ≫ coConnectingAt D n W hW =
      coConnectingAt D n Z hZ ≫ (D.T (n + 1)).map φ.τ₁ := by
  let f : (⟨Z, hZ⟩ : ShortComplex.ShortExactSequences A) ⟶ ⟨W, hW⟩ :=
    ObjectProperty.homMk φ
  exact (D.connecting n).naturality f

private noncomputable def effaceSequenceMap {X Y J I : A}
    (jX : X ⟶ J) (jY : Y ⟶ I) (u : X ⟶ Y) (t : J ⟶ I)
    (hcomm : jX ≫ t = u ≫ jY) :
    ShortComplex.cokernelSequence jX ⟶ ShortComplex.cokernelSequence jY where
  τ₁ := u
  τ₂ := t
  τ₃ := cokernel.map jX jY u t hcomm
  comm₁₂ := hcomm.symm
  comm₂₃ := by
    dsimp only [ShortComplex.cokernelSequence, cokernel.map]
    simp only [cokernel.π_desc]

private theorem effaceDescent_natural {n : ℕ} (f : T.T n ⟶ S.T n)
    {X Y J I : A} (u : X ⟶ Y) (jX : X ⟶ J) (jY : Y ⟶ I) (t : J ⟶ I)
    (hcomm : jX ≫ t = u ≫ jY) (hmX : Mono jX) (hmY : Mono jY)
    (hkX : (T.T (n + 1)).map jX = 0) (hkY : (T.T (n + 1)).map jY = 0) :
    effaceDescent (T := T) (S := S) f jX hmX hkX ≫ (S.T (n + 1)).map u =
      (T.T (n + 1)).map u ≫ effaceDescent (T := T) (S := S) f jY hmY hkY := by
  have := hmX
  have := hmY
  let ZX := ShortComplex.cokernelSequence jX
  let ZY := ShortComplex.cokernelSequence jY
  let hX := ShortComplex.shortExact_cokernelSequence jX
  let hY := ShortComplex.shortExact_cokernelSequence jY
  let φ := effaceSequenceMap jX jY u t hcomm
  let q : cokernel jX ⟶ cokernel jY := φ.τ₃
  let dX : (T.T n).obj (cokernel jX) ⟶ (T.T (n + 1)).obj X :=
    coConnectingAt T n ZX hX
  let dY : (T.T n).obj (cokernel jY) ⟶ (T.T (n + 1)).obj Y :=
    coConnectingAt T n ZY hY
  let sX : (S.T n).obj (cokernel jX) ⟶ (S.T (n + 1)).obj X :=
    coConnectingAt S n ZX hX
  let sY : (S.T n).obj (cokernel jY) ⟶ (S.T (n + 1)).obj Y :=
    coConnectingAt S n ZY hY
  have hepi : Epi dX := effaceConnecting_epi (T := T) jX hkX
  have := hepi
  have hTnat : (T.T n).map q ≫ dY = dX ≫ (T.T (n + 1)).map u :=
    connecting_naturality T n φ hX hY
  have hSnat : (S.T n).map q ≫ sY = sX ≫ (S.T (n + 1)).map u :=
    connecting_naturality S n φ hX hY
  have hXspec : dX ≫ effaceDescent (T := T) (S := S) f jX hmX hkX =
      f.app (cokernel jX) ≫ sX := effaceDescent_spec f jX hmX hkX
  have hYspec : dY ≫ effaceDescent (T := T) (S := S) f jY hmY hkY =
      f.app (cokernel jY) ≫ sY := effaceDescent_spec f jY hmY hkY
  apply (cancel_epi dX).mp
  calc
    dX ≫ (effaceDescent (T := T) (S := S) f jX hmX hkX ≫ (S.T (n + 1)).map u) =
        (f.app (cokernel jX) ≫ sX) ≫ (S.T (n + 1)).map u := by
      rw [← Category.assoc, hXspec]
    _ = f.app (cokernel jX) ≫ ((S.T n).map q ≫ sY) := by
      rw [Category.assoc, ← hSnat]
    _ = ((T.T n).map q ≫ f.app (cokernel jY)) ≫ sY := by
      rw [← Category.assoc, ← f.naturality q]
    _ = (T.T n).map q ≫
        (dY ≫ effaceDescent (T := T) (S := S) f jY hmY hkY) := by
      rw [Category.assoc, hYspec]
    _ = dX ≫ ((T.T (n + 1)).map u ≫
        effaceDescent (T := T) (S := S) f jY hmY hkY) := by
      rw [← Category.assoc, hTnat, Category.assoc]

private theorem effaceDescent_independent {n : ℕ} (f : T.T n ⟶ S.T n)
    {X J₀ J₁ : A} (j₀ : X ⟶ J₀) (j₁ : X ⟶ J₁)
    (hm₀ : Mono j₀) (hm₁ : Mono j₁)
    (hk₀ : (T.T (n + 1)).map j₀ = 0) (hk₁ : (T.T (n + 1)).map j₁ = 0) :
    effaceDescent (T := T) (S := S) f j₀ hm₀ hk₀ =
      effaceDescent (T := T) (S := S) f j₁ hm₁ hk₁ := by
  have := hm₀
  have := hm₁
  have hinl : Mono (pushout.inl j₀ j₁) := Abelian.mono_pushout_of_mono_g j₀ j₁
  have := hinl
  let j := j₀ ≫ pushout.inl j₀ j₁
  have hm : Mono j := mono_comp' hm₀ hinl
  have hk : (T.T (n + 1)).map j = 0 := by
    rw [(T.T (n + 1)).map_comp, hk₀, zero_comp]
  have h₀ : effaceDescent (T := T) (S := S) f j₀ hm₀ hk₀ =
      effaceDescent (T := T) (S := S) f j hm hk := by
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      effaceDescent_natural f (𝟙 X) j₀ j (pushout.inl j₀ j₁)
        (Category.id_comp j).symm hm₀ hm hk₀ hk
  have h₁ : effaceDescent (T := T) (S := S) f j₁ hm₁ hk₁ =
      effaceDescent (T := T) (S := S) f j hm hk := by
    have hcomm : j₁ ≫ pushout.inr j₀ j₁ = (𝟙 X) ≫ j := by
      rw [Category.id_comp]
      exact pushout.condition.symm
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      effaceDescent_natural f (𝟙 X) j₁ j (pushout.inr j₀ j₁) hcomm hm₁ hm hk₁ hk
  exact h₀.trans h₁.symm

private theorem efface_map_biprod_lift {n : ℕ} {X J I : A} (a : X ⟶ J) (b : X ⟶ I)
    (ha : (T.T (n + 1)).map a = 0) (hb : (T.T (n + 1)).map b = 0) :
    (T.T (n + 1)).map (biprod.lift a b) = 0 := by
  have := T.additive (n + 1)
  have := preservesBinaryBiproducts_of_preservesBiproducts (T.T (n + 1))
  rw [← biprod.lift_mapBiprod (T.T (n + 1)) J I a b, ha, hb]
  have hz : biprod.lift
      (0 : (T.T (n + 1)).obj X ⟶ (T.T (n + 1)).obj J)
      (0 : (T.T (n + 1)).obj X ⟶ (T.T (n + 1)).obj I) = 0 := by
    apply biprod.hom_ext
    · simp only [biprod.lift_fst, zero_comp]
    · simp only [biprod.lift_snd, zero_comp]
  rw [hz, zero_comp]

private structure Effacement (F : A ⥤ B) (X : A) where
  /-- The target of the effacing monomorphism. -/
  I : A
  /-- The effacing map. -/
  map : X ⟶ I
  /-- The map is a monomorphism. -/
  mono : Mono map
  /-- The functor kills the map. -/
  kill : F.map map = 0

private noncomputable def chooseEffacement {F : A ⥤ B} (h : F.IsEffaceable) (X : A) :
    Effacement F X :=
  Classical.choice (by
    obtain ⟨I, j, hm, hk⟩ := h X
    exact ⟨⟨I, j, hm, hk⟩⟩)

private noncomputable def successor
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) {n : ℕ} (f : T.T n ⟶ S.T n) :
    T.T (n + 1) ⟶ S.T (n + 1) where
  app X :=
    let e := chooseEffacement (h n) X
    effaceDescent (T := T) (S := S) f e.map e.mono e.kill
  naturality X Y u := by
    let eX := chooseEffacement (h n) X
    let eY := chooseEffacement (h n) Y
    have := eX.mono
    let j := biprod.lift eX.map (u ≫ eY.map)
    have hm : Mono j := biprod.mono_lift_of_mono_left _ _
    have hkY : (T.T (n + 1)).map (u ≫ eY.map) = 0 := by
      rw [(T.T (n + 1)).map_comp, eY.kill, comp_zero]
    have hk : (T.T (n + 1)).map j = 0 :=
      efface_map_biprod_lift eX.map (u ≫ eY.map) eX.kill hkY
    have hi := effaceDescent_independent f eX.map j eX.mono hm eX.kill hk
    have hc : j ≫ biprod.snd = u ≫ eY.map := biprod.lift_snd _ _
    have hn := effaceDescent_natural f u j eY.map biprod.snd hc hm eY.mono hk eY.kill
    change (T.T (n + 1)).map u ≫
        effaceDescent (T := T) (S := S) f eY.map eY.mono eY.kill =
      effaceDescent (T := T) (S := S) f eX.map eX.mono eX.kill ≫ (S.T (n + 1)).map u
    rw [hi]
    exact hn.symm

private theorem successor_spec (h : ∀ n, (T.T (n + 1)).IsEffaceable)
    {n : ℕ} (f : T.T n ⟶ S.T n) {X J : A} (j : X ⟶ J) (hm : Mono j)
    (hk : (T.T (n + 1)).map j = 0) :
    coConnectingAt T n (ShortComplex.cokernelSequence j)
        (letI := hm; ShortComplex.shortExact_cokernelSequence j) ≫
      (successor (S := S) h f).app X =
        f.app (cokernel j) ≫ coConnectingAt S n (ShortComplex.cokernelSequence j)
          (letI := hm; ShortComplex.shortExact_cokernelSequence j) := by
  let e := chooseEffacement (h n) X
  have hi := effaceDescent_independent f e.map j e.mono hm e.kill hk
  let d : (T.T n).obj (cokernel j) ⟶ (T.T (n + 1)).obj X :=
    coConnectingAt T n (ShortComplex.cokernelSequence j)
      (letI := hm; ShortComplex.shortExact_cokernelSequence j)
  exact (congrArg (fun k : (T.T (n + 1)).obj X ⟶ (S.T (n + 1)).obj X => d ≫ k) hi).trans
    (effaceDescent_spec f j hm hk)

private noncomputable def extendedFamily
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) (f₀ : T.T 0 ⟶ S.T 0) :
    (n : ℕ) → T.T n ⟶ S.T n :=
  Nat.rec f₀ (fun _ f => successor h f)

private noncomputable def middleEffaceMap (Z : ShortComplex.ShortExactSequences A)
    {J : A} (j : Z.obj.X₂ ⟶ J) :
    Z.obj ⟶ ShortComplex.cokernelSequence (Z.obj.f ≫ j) where
  τ₁ := 𝟙 Z.obj.X₁
  τ₂ := j
  τ₃ := (CokernelCofork.IsColimit.desc' Z.property.gIsCokernel
    (j ≫ cokernel.π (Z.obj.f ≫ j)) (by
      rw [← Category.assoc, cokernel.condition])).1
  comm₁₂ := Category.id_comp _
  comm₂₃ := (CokernelCofork.IsColimit.desc' Z.property.gIsCokernel
    (j ≫ cokernel.π (Z.obj.f ≫ j)) (by
      rw [← Category.assoc, cokernel.condition])).2.symm

private theorem extendedFamily_comm
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) (f₀ : T.T 0 ⟶ S.T 0)
    (n : ℕ) (Z : ShortComplex.ShortExactSequences A) :
    (T.connecting n).app Z ≫ (extendedFamily h f₀ (n + 1)).app Z.obj.X₁ =
      (extendedFamily h f₀ n).app Z.obj.X₃ ≫ (S.connecting n).app Z := by
  let e := chooseEffacement (h n) Z.obj.X₂
  have := Z.property.mono_f
  have := e.mono
  let j := Z.obj.f ≫ e.map
  have hm : Mono j := mono_comp' Z.property.mono_f e.mono
  have hk : (T.T (n + 1)).map j = 0 := by
    rw [(T.T (n + 1)).map_comp, e.kill, comp_zero]
  have := hm
  let R := ShortComplex.cokernelSequence j
  let hR := ShortComplex.shortExact_cokernelSequence j
  let φ := middleEffaceMap Z e.map
  let q : Z.obj.X₃ ⟶ cokernel j := φ.τ₃
  let dR : (T.T n).obj (cokernel j) ⟶ (T.T (n + 1)).obj Z.obj.X₁ :=
    coConnectingAt T n R hR
  let sR : (S.T n).obj (cokernel j) ⟶ (S.T (n + 1)).obj Z.obj.X₁ :=
    coConnectingAt S n R hR
  let dZ : (T.T n).obj Z.obj.X₃ ⟶ (T.T (n + 1)).obj Z.obj.X₁ :=
    coConnectingAt T n Z.obj Z.property
  let sZ : (S.T n).obj Z.obj.X₃ ⟶ (S.T (n + 1)).obj Z.obj.X₁ :=
    coConnectingAt S n Z.obj Z.property
  have hTnat : (T.T n).map q ≫ dR = dZ := by
    have ht := connecting_naturality T n φ Z.property hR
    change (T.T n).map q ≫ dR = dZ ≫ (T.T (n + 1)).map (𝟙 Z.obj.X₁) at ht
    rw [Functor.map_id, Category.comp_id] at ht
    exact ht
  have hSnat : (S.T n).map q ≫ sR = sZ := by
    have ht := connecting_naturality S n φ Z.property hR
    change (S.T n).map q ≫ sR = sZ ≫ (S.T (n + 1)).map (𝟙 Z.obj.X₁) at ht
    rw [Functor.map_id, Category.comp_id] at ht
    exact ht
  have hs : dR ≫ (successor h (extendedFamily h f₀ n)).app Z.obj.X₁ =
      (extendedFamily h f₀ n).app (cokernel j) ≫ sR :=
    successor_spec h (extendedFamily h f₀ n) j hm hk
  change dZ ≫ (successor h (extendedFamily h f₀ n)).app Z.obj.X₁ =
    (extendedFamily h f₀ n).app Z.obj.X₃ ≫ sZ
  rw [← hTnat, Category.assoc, hs, ← Category.assoc,
    (extendedFamily h f₀ n).naturality q, Category.assoc, hSnat]

/-- Positive-degree effacements extend a degree-zero natural transformation to
a morphism of cohomological δ-functors. -/
@[no_expose]
noncomputable def extendOfEffaceable (T S : CohomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) (f₀ : T.T 0 ⟶ S.T 0) : T ⟶ S := by
  exact homMk A B (extendedFamily h f₀) (extendedFamily_comm h f₀)

/-- The extension has the prescribed degree-zero component. -/
@[simp]
theorem extendOfEffaceable_app_zero (T S : CohomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) (f₀ : T.T 0 ⟶ S.T 0) :
    Hom.app (extendOfEffaceable T S h f₀) 0 = f₀ := by
  rfl

/-- A cohomological extension from an effaceable δ-functor is determined by its
degree-zero component. -/
theorem extendOfEffaceable_unique (T S : CohomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) (f₀ : T.T 0 ⟶ S.T 0)
    (g : T ⟶ S) (hg : Hom.app g 0 = f₀) : g = extendOfEffaceable T S h f₀ := by
  have heq : ∀ n, Hom.app g n = extendedFamily h f₀ n := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih =>
        apply NatTrans.ext
        funext X
        let e := chooseEffacement (h n) X
        have := e.mono
        let Z := ShortComplex.cokernelSequence e.map
        let hZ := ShortComplex.shortExact_cokernelSequence e.map
        let dT : (T.T n).obj (cokernel e.map) ⟶ (T.T (n + 1)).obj X :=
          coConnectingAt T n Z hZ
        have hepi : Epi dT := effaceConnecting_epi (T := T) e.map e.kill
        have := hepi
        apply (cancel_epi dT).mp
        have hc := DeltaFunctor.System.comm g.hom n ⟨Z, hZ⟩
        change dT ≫ (Hom.app g (n + 1)).app X =
          (Hom.app g n).app (cokernel e.map) ≫ coConnectingAt S n Z hZ at hc
        have hs := successor_spec h (extendedFamily h f₀ n) e.map e.mono e.kill
        change dT ≫ (Hom.app g (n + 1)).app X =
          dT ≫ (successor h (extendedFamily h f₀ n)).app X
        rw [hc, ih]
        exact hs.symm
  apply hom_ext
  intro n
  change Hom.app g n = extendedFamily h f₀ n
  exact heq n

/-- A cohomological δ-functor effaceable in every positive degree is universal. -/
theorem isUniversal_of_effaceable (T : CohomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsEffaceable) : IsUniversal A B T := by
  intro S f₀
  refine ⟨extendOfEffaceable T S h f₀, extendOfEffaceable_app_zero T S h f₀, ?_⟩
  intro g hg
  exact extendOfEffaceable_unique T S h f₀ g hg

end CohomologicalDeltaFunctor

namespace HomologicalDeltaFunctor

variable {T S : HomologicalDeltaFunctor A B}

private theorem coeffaceConnecting_mono {n : ℕ} {P X : A} (e : P ⟶ X) [Epi e]
    (hkill : (T.T (n + 1)).map e = 0) :
    Mono (hoConnectingAt T n (ShortComplex.kernelSequence e)
      (ShortComplex.kernelSequence_shortExact e)) := by
  obtain ⟨w, hex⟩ := T.exactRight n
    ⟨ShortComplex.kernelSequence e, ShortComplex.kernelSequence_shortExact e⟩
  have hk : (T.T (n + 1)).map (ShortComplex.kernelSequence e).g = 0 := by
    change (T.T (n + 1)).map e = 0
    exact hkill
  exact (ShortComplex.exact_iff_mono _ hk).mp hex

private theorem coeffaceLift_condition {n : ℕ} (f : S.T n ⟶ T.T n)
    {P X : A} (e : P ⟶ X) [Epi e] :
    (hoConnectingAt S n (ShortComplex.kernelSequence e)
        (ShortComplex.kernelSequence_shortExact e) ≫ f.app (kernel e)) ≫
      cokernel.π (hoConnectingAt T n (ShortComplex.kernelSequence e)
        (ShortComplex.kernelSequence_shortExact e)) = 0 := by
  let Z := ShortComplex.kernelSequence e
  let hZ := ShortComplex.kernelSequence_shortExact e
  let dT := hoConnectingAt T n Z hZ
  let dS := hoConnectingAt S n Z hZ
  obtain ⟨wT, hex⟩ := T.exactLeft n ⟨Z, hZ⟩
  change dT ≫ (T.T n).map Z.f = 0 at wT
  change (ShortComplex.mk dT ((T.T n).map Z.f) wT).Exact at hex
  have hm : Mono (cokernel.desc dT ((T.T n).map Z.f) wT) := hex.mono_cokernelDesc
  have := hm
  obtain ⟨wS, -⟩ := S.exactLeft n ⟨Z, hZ⟩
  change dS ≫ (S.T n).map Z.f = 0 at wS
  have hzero : ((dS ≫ f.app Z.X₁) ≫ cokernel.π dT) ≫
      cokernel.desc dT ((T.T n).map Z.f) wT =
        0 ≫ cokernel.desc dT ((T.T n).map Z.f) wT := by
    rw [Category.assoc, cokernel.π_desc, Category.assoc, ← f.naturality Z.f,
      ← Category.assoc, wS, zero_comp, zero_comp]
  exact (cancel_mono _).mp hzero

private noncomputable def coeffaceLift {n : ℕ} (f : S.T n ⟶ T.T n)
    {P X : A} (e : P ⟶ X) (he : Epi e)
    (hkill : (T.T (n + 1)).map e = 0) :
    (S.T (n + 1)).obj X ⟶ (T.T (n + 1)).obj X := by
  letI := he
  letI := coeffaceConnecting_mono (T := T) e hkill
  exact Abelian.monoLift
    (hoConnectingAt T n (ShortComplex.kernelSequence e) (ShortComplex.kernelSequence_shortExact e))
    (hoConnectingAt S n (ShortComplex.kernelSequence e)
      (ShortComplex.kernelSequence_shortExact e) ≫ f.app (kernel e))
    (coeffaceLift_condition (T := T) (S := S) f e)

private theorem coeffaceLift_spec {n : ℕ} (f : S.T n ⟶ T.T n)
    {P X : A} (e : P ⟶ X) (he : Epi e)
    (hkill : (T.T (n + 1)).map e = 0) :
    coeffaceLift (T := T) (S := S) f e he hkill ≫
      hoConnectingAt T n (ShortComplex.kernelSequence e)
        (letI := he; ShortComplex.kernelSequence_shortExact e) =
      hoConnectingAt S n (ShortComplex.kernelSequence e)
        (letI := he; ShortComplex.kernelSequence_shortExact e) ≫ f.app (kernel e) := by
  unfold coeffaceLift
  have := he
  let dT : (T.T (n + 1)).obj X ⟶ (T.T n).obj (kernel e) :=
    hoConnectingAt T n (ShortComplex.kernelSequence e) (ShortComplex.kernelSequence_shortExact e)
  have hmono : Mono dT := coeffaceConnecting_mono (T := T) e hkill
  have := hmono
  exact Abelian.monoLift_comp dT _ _

private theorem connecting_naturality (D : HomologicalDeltaFunctor A B) (n : ℕ)
    {Z W : ShortComplex A} (φ : Z ⟶ W) (hZ : Z.ShortExact) (hW : W.ShortExact) :
    (D.T (n + 1)).map φ.τ₃ ≫ hoConnectingAt D n W hW =
      hoConnectingAt D n Z hZ ≫ (D.T n).map φ.τ₁ := by
  let f : (⟨Z, hZ⟩ : ShortComplex.ShortExactSequences A) ⟶ ⟨W, hW⟩ :=
    ObjectProperty.homMk φ
  exact (D.connecting n).naturality f

private noncomputable def coeffaceSequenceMap {X Y P Q : A}
    (eX : P ⟶ X) (eY : Q ⟶ Y) (u : X ⟶ Y) (s : P ⟶ Q)
    (hcomm : s ≫ eY = eX ≫ u) :
    ShortComplex.kernelSequence eX ⟶ ShortComplex.kernelSequence eY where
  τ₁ := kernel.map eX eY s u hcomm.symm
  τ₂ := s
  τ₃ := u
  comm₁₂ := by
    dsimp only [ShortComplex.kernelSequence, kernel.map]
    simp only [kernel.lift_ι]
  comm₂₃ := hcomm

private theorem coeffaceLift_natural {n : ℕ} (f : S.T n ⟶ T.T n)
    {X Y P Q : A} (u : X ⟶ Y) (eX : P ⟶ X) (eY : Q ⟶ Y) (s : P ⟶ Q)
    (hcomm : s ≫ eY = eX ≫ u) (heX : Epi eX) (heY : Epi eY)
    (hkX : (T.T (n + 1)).map eX = 0) (hkY : (T.T (n + 1)).map eY = 0) :
    (S.T (n + 1)).map u ≫ coeffaceLift (T := T) (S := S) f eY heY hkY =
      coeffaceLift (T := T) (S := S) f eX heX hkX ≫ (T.T (n + 1)).map u := by
  have := heX
  have := heY
  let ZX := ShortComplex.kernelSequence eX
  let ZY := ShortComplex.kernelSequence eY
  let hX := ShortComplex.kernelSequence_shortExact eX
  let hY := ShortComplex.kernelSequence_shortExact eY
  let φ := coeffaceSequenceMap eX eY u s hcomm
  let q : kernel eX ⟶ kernel eY := φ.τ₁
  let dX : (T.T (n + 1)).obj X ⟶ (T.T n).obj (kernel eX) :=
    hoConnectingAt T n ZX hX
  let dY : (T.T (n + 1)).obj Y ⟶ (T.T n).obj (kernel eY) :=
    hoConnectingAt T n ZY hY
  let sX : (S.T (n + 1)).obj X ⟶ (S.T n).obj (kernel eX) :=
    hoConnectingAt S n ZX hX
  let sY : (S.T (n + 1)).obj Y ⟶ (S.T n).obj (kernel eY) :=
    hoConnectingAt S n ZY hY
  have hmono : Mono dY := coeffaceConnecting_mono (T := T) eY hkY
  have := hmono
  have hTnat : (T.T (n + 1)).map u ≫ dY = dX ≫ (T.T n).map q :=
    connecting_naturality T n φ hX hY
  have hSnat : (S.T (n + 1)).map u ≫ sY = sX ≫ (S.T n).map q :=
    connecting_naturality S n φ hX hY
  have hXspec : coeffaceLift (T := T) (S := S) f eX heX hkX ≫ dX =
      sX ≫ f.app (kernel eX) := coeffaceLift_spec f eX heX hkX
  have hYspec : coeffaceLift (T := T) (S := S) f eY heY hkY ≫ dY =
      sY ≫ f.app (kernel eY) := coeffaceLift_spec f eY heY hkY
  apply (cancel_mono dY).mp
  calc
    ((S.T (n + 1)).map u ≫ coeffaceLift (T := T) (S := S) f eY heY hkY) ≫ dY =
        (S.T (n + 1)).map u ≫ (sY ≫ f.app (kernel eY)) := by
      rw [Category.assoc, hYspec]
    _ = (sX ≫ (S.T n).map q) ≫ f.app (kernel eY) := by
      rw [← Category.assoc, hSnat]
    _ = (sX ≫ f.app (kernel eX)) ≫ (T.T n).map q := by
      rw [Category.assoc, f.naturality q, ← Category.assoc]
    _ = (coeffaceLift (T := T) (S := S) f eX heX hkX ≫ dX) ≫ (T.T n).map q := by
      rw [← hXspec]
    _ = (coeffaceLift (T := T) (S := S) f eX heX hkX ≫ (T.T (n + 1)).map u) ≫ dY := by
      rw [Category.assoc, ← hTnat, ← Category.assoc]

private theorem coeffaceLift_independent {n : ℕ} (f : S.T n ⟶ T.T n)
    {P₀ P₁ X : A} (e₀ : P₀ ⟶ X) (e₁ : P₁ ⟶ X)
    (he₀ : Epi e₀) (he₁ : Epi e₁)
    (hk₀ : (T.T (n + 1)).map e₀ = 0) (hk₁ : (T.T (n + 1)).map e₁ = 0) :
    coeffaceLift (T := T) (S := S) f e₀ he₀ hk₀ =
      coeffaceLift (T := T) (S := S) f e₁ he₁ hk₁ := by
  have := he₀
  have := he₁
  have hfst : Epi (pullback.fst e₀ e₁) := Abelian.epi_pullback_of_epi_g e₀ e₁
  have := hfst
  let e := pullback.fst e₀ e₁ ≫ e₀
  have he : Epi e := epi_comp' hfst he₀
  have hk : (T.T (n + 1)).map e = 0 := by
    rw [(T.T (n + 1)).map_comp, hk₀, comp_zero]
  have h₀ : coeffaceLift (T := T) (S := S) f e₀ he₀ hk₀ =
      coeffaceLift (T := T) (S := S) f e he hk := by
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      coeffaceLift_natural f (𝟙 X) e e₀ (pullback.fst e₀ e₁)
        (Category.comp_id e).symm he he₀ hk hk₀
  have h₁ : coeffaceLift (T := T) (S := S) f e₁ he₁ hk₁ =
      coeffaceLift (T := T) (S := S) f e he hk := by
    have hcomm : pullback.snd e₀ e₁ ≫ e₁ = e ≫ 𝟙 X := by
      rw [Category.comp_id]
      exact pullback.condition.symm
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      coeffaceLift_natural f (𝟙 X) e e₁ (pullback.snd e₀ e₁) hcomm he he₁ hk hk₁
  exact h₀.trans h₁.symm

private theorem coefface_map_biprod_desc {n : ℕ} {P Q Y : A} (a : P ⟶ Y) (b : Q ⟶ Y)
    (ha : (T.T (n + 1)).map a = 0) (hb : (T.T (n + 1)).map b = 0) :
    (T.T (n + 1)).map (biprod.desc a b) = 0 := by
  have := T.additive (n + 1)
  have := preservesBinaryBiproducts_of_preservesBiproducts (T.T (n + 1))
  rw [← biprod.mapBiprod_hom_desc (T.T (n + 1)) P Q a b, ha, hb]
  have hz : biprod.desc
      (0 : (T.T (n + 1)).obj P ⟶ (T.T (n + 1)).obj Y)
      (0 : (T.T (n + 1)).obj Q ⟶ (T.T (n + 1)).obj Y) = 0 := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc, comp_zero]
    · simp only [biprod.inr_desc, comp_zero]
  rw [hz, comp_zero]

private structure Coeffacement (F : A ⥤ B) (X : A) where
  /-- The source of the coeffacing epimorphism. -/
  P : A
  /-- The coeffacing map. -/
  map : P ⟶ X
  /-- The map is an epimorphism. -/
  epi : Epi map
  /-- The functor kills the map. -/
  kill : F.map map = 0

private noncomputable def chooseCoeffacement {F : A ⥤ B} (h : F.IsCoeffaceable) (X : A) :
    Coeffacement F X :=
  Classical.choice (by
    obtain ⟨P, e, he, hk⟩ := h X
    exact ⟨⟨P, e, he, hk⟩⟩)

private noncomputable def successor
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) {n : ℕ} (f : S.T n ⟶ T.T n) :
    S.T (n + 1) ⟶ T.T (n + 1) where
  app X :=
    let e := chooseCoeffacement (h n) X
    coeffaceLift (T := T) (S := S) f e.map e.epi e.kill
  naturality X Y u := by
    let eX := chooseCoeffacement (h n) X
    let eY := chooseCoeffacement (h n) Y
    have := eY.epi
    let e := biprod.desc (eX.map ≫ u) eY.map
    have he : Epi e := biprod.epi_desc_of_epi_right _ _
    have hkX : (T.T (n + 1)).map (eX.map ≫ u) = 0 := by
      rw [(T.T (n + 1)).map_comp, eX.kill, zero_comp]
    have hk : (T.T (n + 1)).map e = 0 :=
      coefface_map_biprod_desc (eX.map ≫ u) eY.map hkX eY.kill
    have hi := coeffaceLift_independent f eY.map e eY.epi he eY.kill hk
    have hc : biprod.inl ≫ e = eX.map ≫ u := biprod.inl_desc _ _
    have hn := coeffaceLift_natural f u eX.map e biprod.inl hc eX.epi he eX.kill hk
    change (S.T (n + 1)).map u ≫
        coeffaceLift (T := T) (S := S) f eY.map eY.epi eY.kill =
      coeffaceLift (T := T) (S := S) f eX.map eX.epi eX.kill ≫ (T.T (n + 1)).map u
    rw [hi]
    exact hn

private theorem successor_spec (h : ∀ n, (T.T (n + 1)).IsCoeffaceable)
    {n : ℕ} (f : S.T n ⟶ T.T n) {P X : A} (e : P ⟶ X) (he : Epi e)
    (hk : (T.T (n + 1)).map e = 0) :
    (successor (S := S) h f).app X ≫
      hoConnectingAt T n (ShortComplex.kernelSequence e)
        (letI := he; ShortComplex.kernelSequence_shortExact e) =
      hoConnectingAt S n (ShortComplex.kernelSequence e)
        (letI := he; ShortComplex.kernelSequence_shortExact e) ≫ f.app (kernel e) := by
  let e' := chooseCoeffacement (h n) X
  have hi := coeffaceLift_independent f e'.map e e'.epi he e'.kill hk
  let d : (T.T (n + 1)).obj X ⟶ (T.T n).obj (kernel e) :=
    hoConnectingAt T n (ShortComplex.kernelSequence e)
      (letI := he; ShortComplex.kernelSequence_shortExact e)
  exact (congrArg (fun k : (S.T (n + 1)).obj X ⟶ (T.T (n + 1)).obj X => k ≫ d) hi).trans
    (coeffaceLift_spec f e he hk)

private noncomputable def extendedFamily
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) (f₀ : S.T 0 ⟶ T.T 0) :
    (n : ℕ) → S.T n ⟶ T.T n :=
  Nat.rec f₀ (fun _ f => successor h f)

private noncomputable def middleCoeffaceMap (Z : ShortComplex.ShortExactSequences A)
    {P : A} (e : P ⟶ Z.obj.X₂) :
    ShortComplex.kernelSequence (e ≫ Z.obj.g) ⟶ Z.obj where
  τ₁ := (KernelFork.IsLimit.lift' Z.property.fIsKernel
    (kernel.ι (e ≫ Z.obj.g) ≫ e) (by
      rw [Category.assoc, kernel.condition])).1
  τ₂ := e
  τ₃ := 𝟙 Z.obj.X₃
  comm₁₂ := (KernelFork.IsLimit.lift' Z.property.fIsKernel
    (kernel.ι (e ≫ Z.obj.g) ≫ e) (by
      rw [Category.assoc, kernel.condition])).2
  comm₂₃ := (Category.comp_id _).symm

private theorem extendedFamily_comm
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) (f₀ : S.T 0 ⟶ T.T 0)
    (n : ℕ) (Z : ShortComplex.ShortExactSequences A) :
    (S.connecting n).app Z ≫ (extendedFamily h f₀ n).app Z.obj.X₁ =
      (extendedFamily h f₀ (n + 1)).app Z.obj.X₃ ≫ (T.connecting n).app Z := by
  let e₂ := chooseCoeffacement (h n) Z.obj.X₂
  have := Z.property.epi_g
  have := e₂.epi
  let e := e₂.map ≫ Z.obj.g
  have he : Epi e := epi_comp' e₂.epi Z.property.epi_g
  have hk : (T.T (n + 1)).map e = 0 := by
    rw [(T.T (n + 1)).map_comp, e₂.kill, zero_comp]
  have := he
  let R := ShortComplex.kernelSequence e
  let hR := ShortComplex.kernelSequence_shortExact e
  let φ := middleCoeffaceMap Z e₂.map
  let q : kernel e ⟶ Z.obj.X₁ := φ.τ₁
  let dR : (T.T (n + 1)).obj Z.obj.X₃ ⟶ (T.T n).obj (kernel e) :=
    hoConnectingAt T n R hR
  let sR : (S.T (n + 1)).obj Z.obj.X₃ ⟶ (S.T n).obj (kernel e) :=
    hoConnectingAt S n R hR
  let dZ : (T.T (n + 1)).obj Z.obj.X₃ ⟶ (T.T n).obj Z.obj.X₁ :=
    hoConnectingAt T n Z.obj Z.property
  let sZ : (S.T (n + 1)).obj Z.obj.X₃ ⟶ (S.T n).obj Z.obj.X₁ :=
    hoConnectingAt S n Z.obj Z.property
  have hTnat : dZ = dR ≫ (T.T n).map q := by
    have ht := connecting_naturality T n φ hR Z.property
    change (T.T (n + 1)).map (𝟙 Z.obj.X₃) ≫ dZ = dR ≫ (T.T n).map q at ht
    rw [Functor.map_id, Category.id_comp] at ht
    exact ht
  have hSnat : sZ = sR ≫ (S.T n).map q := by
    have ht := connecting_naturality S n φ hR Z.property
    change (S.T (n + 1)).map (𝟙 Z.obj.X₃) ≫ sZ = sR ≫ (S.T n).map q at ht
    rw [Functor.map_id, Category.id_comp] at ht
    exact ht
  have hs : (successor h (extendedFamily h f₀ n)).app Z.obj.X₃ ≫ dR =
      sR ≫ (extendedFamily h f₀ n).app (kernel e) :=
    successor_spec h (extendedFamily h f₀ n) e he hk
  change sZ ≫ (extendedFamily h f₀ n).app Z.obj.X₁ =
    (successor h (extendedFamily h f₀ n)).app Z.obj.X₃ ≫ dZ
  rw [hSnat, Category.assoc, (extendedFamily h f₀ n).naturality q,
    ← Category.assoc, ← hs, Category.assoc, ← hTnat]

/-- Positive-degree coeffacements of the target extend a degree-zero natural
transformation to a morphism of homological δ-functors. -/
@[no_expose]
noncomputable def extendOfCoeffaceable (S T : HomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) (f₀ : S.T 0 ⟶ T.T 0) : S ⟶ T := by
  exact homMk A B (extendedFamily h f₀) (extendedFamily_comm h f₀)

/-- The extension has the prescribed degree-zero component. -/
@[simp]
theorem extendOfCoeffaceable_app_zero (S T : HomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) (f₀ : S.T 0 ⟶ T.T 0) :
    Hom.app (extendOfCoeffaceable S T h f₀) 0 = f₀ := by
  rfl

/-- A homological extension into a coeffaceable δ-functor is determined by its
degree-zero component. -/
theorem extendOfCoeffaceable_unique (S T : HomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) (f₀ : S.T 0 ⟶ T.T 0)
    (g : S ⟶ T) (hg : Hom.app g 0 = f₀) : g = extendOfCoeffaceable S T h f₀ := by
  have heq : ∀ n, Hom.app g n = extendedFamily h f₀ n := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih =>
        apply NatTrans.ext
        funext X
        let e := chooseCoeffacement (h n) X
        have := e.epi
        let Z := ShortComplex.kernelSequence e.map
        let hZ := ShortComplex.kernelSequence_shortExact e.map
        let dT : (T.T (n + 1)).obj X ⟶ (T.T n).obj (kernel e.map) :=
          hoConnectingAt T n Z hZ
        have hmono : Mono dT := coeffaceConnecting_mono (T := T) e.map e.kill
        have := hmono
        apply (cancel_mono dT).mp
        have hc := DeltaFunctor.System.comm g.hom n ⟨Z, hZ⟩
        change hoConnectingAt S n Z hZ ≫ (Hom.app g n).app (kernel e.map) =
          (Hom.app g (n + 1)).app X ≫ dT at hc
        have hs := successor_spec h (extendedFamily h f₀ n) e.map e.epi e.kill
        change (Hom.app g (n + 1)).app X ≫ dT =
          (successor h (extendedFamily h f₀ n)).app X ≫ dT
        rw [← hc, ih]
        exact hs.symm
  apply hom_ext
  intro n
  change Hom.app g n = extendedFamily h f₀ n
  exact heq n

/-- A homological δ-functor coeffaceable in every positive degree is universal. -/
theorem isUniversal_of_coeffaceable (T : HomologicalDeltaFunctor A B)
    (h : ∀ n, (T.T (n + 1)).IsCoeffaceable) : IsUniversal A B T := by
  intro S f₀
  refine ⟨extendOfCoeffaceable S T h f₀, extendOfCoeffaceable_app_zero S T h f₀, ?_⟩
  intro g hg
  exact extendOfCoeffaceable_unique S T h f₀ g hg

end HomologicalDeltaFunctor

end Abelian

end CategoryTheory
