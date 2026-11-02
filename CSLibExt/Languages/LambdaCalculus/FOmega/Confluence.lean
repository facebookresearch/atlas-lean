/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Conversion
public import Cslib.Foundations.Relation.Confluence

/-! # Type-beta confluence and conversion inversion

Parallel reduction contracts any set of type-beta redexes. Complete
development proves its diamond property; confluence is not assumed and
normalization or decidability of conversion is not claimed.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega.Ty

/-- Parallel type-beta reduction, retaining the context and kind indices. -/
inductive Par : {Δ : List Kind} → {κ : Kind} → Ty Δ κ → Ty Δ κ → Prop where
  | var {Δ : List Kind} {κ : Kind} (x : KVar Δ κ) : Par (.var x) (.var x)
  | lam {Δ : List Kind} {κ μ : Kind} {b c : Ty (κ :: Δ) μ} :
      Par b c → Par (.lam b) (.lam c)
  | app {Δ : List Kind} {κ μ : Kind}
      {f g : Ty Δ (.arrow κ μ)} {a b : Ty Δ κ} :
      Par f g → Par a b → Par (.app f a) (.app g b)
  | arr {Δ : List Kind} {a a' b b' : Ty Δ .star} :
      Par a a' → Par b b' → Par (.arr a b) (.arr a' b')
  | all {Δ : List Kind} {κ : Kind} {b c : Ty (κ :: Δ) .star} :
      Par b c → Par (.all b) (.all c)
  | beta {Δ : List Kind} {κ μ : Kind}
      {b c : Ty (κ :: Δ) μ} {a a' : Ty Δ κ} :
      Par b c → Par a a' → Par (.app (.lam b) a) (instantiate c a')

variable {Δ Ε : List Kind} {κ μ : Kind} {a b : Ty Δ κ}

/-- Parallel reduction is reflexive on every kinded operator. -/
theorem Par.refl (a : Ty Δ κ) : Par a a := by
  induction a with
  | var x => exact .var x
  | lam b ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | arr a b iha ihb => exact .arr iha ihb
  | all b ih => exact .all ih

/-- Parallel beta reduction is stable under kinded renaming. -/
theorem Par.rename (h : Par a b) (ρ : KRen Δ Ε) :
    Par (Ty.rename ρ a) (Ty.rename ρ b) := by
  induction h generalizing Ε with
  | var x => exact .var (ρ x)
  | lam h ih => exact .lam (ih (KRen.lift ρ))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | arr h₁ h₂ ih₁ ih₂ => exact .arr (ih₁ ρ) (ih₂ ρ)
  | all h ih => exact .all (ih (KRen.lift ρ))
  | beta h₁ h₂ ih₁ ih₂ =>
    rw [rename_instantiate]
    exact .beta (ih₁ (KRen.lift ρ)) (ih₂ ρ)

private theorem par_liftSub {σ τ : Sub Δ Ε}
    (h : ∀ {ν} (x : KVar Δ ν), Par (σ x) (τ x)) {ν : Kind}
    (x : KVar (μ :: Δ) ν) : Par (liftSub σ x) (liftSub τ x) := by
  cases x with
  | zero => exact .var .zero
  | succ x => exact (h x).rename KVar.succ

/-- Parallel reduction respects simultaneous substitution on both sides. -/
theorem Par.subst (h : Par a b) {σ τ : Sub Δ Ε}
    (hσ : ∀ {ν} (x : KVar Δ ν), Par (σ x) (τ x)) :
    Par (Ty.subst σ a) (Ty.subst τ b) := by
  induction h generalizing Ε with
  | var x => exact hσ x
  | lam h ih => exact .lam (ih (fun x => par_liftSub hσ x))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ hσ) (ih₂ hσ)
  | arr h₁ h₂ ih₁ ih₂ => exact .arr (ih₁ hσ) (ih₂ hσ)
  | all h ih => exact .all (ih (fun x => par_liftSub hσ x))
  | beta h₁ h₂ ih₁ ih₂ =>
    rw [subst_instantiate]
    exact .beta (ih₁ (fun x => par_liftSub hσ x)) (ih₂ hσ)

/-- Parallel reduction respects discharging a binder and reducing its image. -/
theorem Par.instantiate {b c : Ty (μ :: Δ) κ} {a a' : Ty Δ μ}
    (hb : Par b c) (ha : Par a a') :
    Par (Ty.instantiate b a) (Ty.instantiate c a') := by
  apply hb.subst
  intro ν x
  cases x with
  | zero => exact ha
  | succ x => exact .var x

/-- Contract all originally present type-beta redexes recursively. -/
def develop : {Δ : List Kind} → {κ : Kind} → Ty Δ κ → Ty Δ κ
  | _, _, .var x => .var x
  | _, _, .lam b => .lam (develop b)
  | _, _, .app (.lam b) a => instantiate (develop b) (develop a)
  | _, _, .app f a => .app (develop f) (develop a)
  | _, _, .arr a b => .arr (develop a) (develop b)
  | _, _, .all b => .all (develop b)

/-- Every parallel reduct reduces to the original complete development. -/
theorem Par.to_develop (h : Par a b) : Par b (develop a) := by
  induction h with
  | var x => exact .var x
  | lam h ih => exact .lam ih
  | arr h₁ h₂ ih₁ ih₂ => exact .arr ih₁ ih₂
  | all h ih => exact .all ih
  | beta h₁ h₂ ih₁ ih₂ => exact ih₁.instantiate ih₂
  | @app Δ κ μ f g a b hf ha ihf iha =>
    cases f with
    | var x => exact .app ihf iha
    | app f a => exact .app ihf iha
    | lam body =>
      cases hf with
      | lam hb =>
        cases ihf with
        | lam ihb => exact .beta ihb iha

/-- Parallel beta reduction has the diamond property at each kind. -/
theorem par_diamond : Relation.Diamond (Par (Δ := Δ) (κ := κ)) := by
  intro a b c hab hac
  exact ⟨develop a, hab.to_develop, hac.to_develop⟩

/-- Parallel type-beta reduction is confluent; no termination premise. -/
theorem par_confluent : Relation.Confluent (Par (Δ := Δ) (κ := κ)) := by
  intro a b c hab hac
  induction hab with
  | refl => exact ⟨c, hac, .refl⟩
  | tail h p ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    obtain ⟨e, hbe, hde⟩ :=
      Relation.DiamondCommute.diamond_commute_reflTransGen_right
        par_diamond p hbd
    exact ⟨e, hbe, hcd.tail hde⟩

/-- Finitely many parallel beta reductions, including zero reductions. -/
abbrev Red (a b : Ty Δ κ) := Relation.ReflTransGen Par a b

/-- Multiple parallel reductions are stable under an operator binder. -/
theorem Red.lam {b c : Ty (μ :: Δ) κ} (h : Red b c) :
    Red (.lam b) (.lam c) :=
  h.lift Ty.lam (fun _ _ => Par.lam)

/-- Multiple parallel reductions are stable under a universal binder. -/
theorem Red.all {b c : Ty (μ :: Δ) .star} (h : Red b c) :
    Red (.all b) (.all c) :=
  h.lift Ty.all (fun _ _ => Par.all)

/-- Multiple reductions are congruent in both type-application arguments. -/
theorem Red.app {f g : Ty Δ (.arrow μ κ)} {a b : Ty Δ μ}
    (hf : Red f g) (ha : Red a b) : Red (.app f a) (.app g b) :=
  (hf.lift (fun f => Ty.app f a)
    (fun _ _ h => Par.app h (.refl _))).trans
  (ha.lift (Ty.app g) (fun _ _ h => Par.app (.refl _) h))

/-- Multiple reductions are congruent in both term-function type arguments. -/
theorem Red.arr {a a' b b' : Ty Δ .star}
    (ha : Red a a') (hb : Red b b') : Red (.arr a b) (.arr a' b') :=
  (ha.lift (fun a => Ty.arr a b)
    (fun _ _ h => Par.arr h (.refl _))).trans
  (hb.lift (Ty.arr a') (fun _ _ h => Par.arr (.refl _) h))

/-- Conversion entails a common parallel-beta reduct (Church-Rosser). -/
theorem Conv.join (h : Conv a b) : ∃ c, Red a c ∧ Red b c := by
  induction h with
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm h ih => obtain ⟨c, hc, hd⟩ := ih; exact ⟨c, hd, hc⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨c, hac, hbc⟩ := ih₁
    obtain ⟨d, hbd, hed⟩ := ih₂
    obtain ⟨z, hcz, hdz⟩ := par_confluent hbc hbd
    exact ⟨z, hac.trans hcz, hed.trans hdz⟩
  | beta body arg => exact ⟨_, .single (.beta (.refl _) (.refl _)), .refl⟩
  | lam h ih => obtain ⟨c, hc, hd⟩ := ih; exact ⟨.lam c, hc.lam, hd.lam⟩
  | all h ih => obtain ⟨c, hc, hd⟩ := ih; exact ⟨.all c, hc.all, hd.all⟩
  | app h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f, hf, hg⟩ := ih₁
    obtain ⟨a, ha, hb⟩ := ih₂
    exact ⟨.app f a, hf.app ha, hg.app hb⟩
  | arr h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a, ha, hb⟩ := ih₁
    obtain ⟨b, hc, hd⟩ := ih₂
    exact ⟨.arr a b, ha.arr hc, hb.arr hd⟩

/-- Every parallel-beta reduction is a proved conversion. -/
theorem Par.conv (h : Par a b) : Conv a b := by
  induction h with
  | var => exact .refl _
  | lam h ih => exact .lam ih
  | app h₁ h₂ ih₁ ih₂ => exact .app ih₁ ih₂
  | arr h₁ h₂ ih₁ ih₂ => exact .arr ih₁ ih₂
  | all h ih => exact .all ih
  | beta h₁ h₂ ih₁ ih₂ =>
    exact .trans (.app (.lam ih₁) ih₂) (.beta _ _)

/-- Finitely many parallel-beta reductions are a proved conversion. -/
theorem Red.conv (h : Red a b) : Conv a b := by
  induction h with
  | refl => exact .refl _
  | tail h p ih => exact .trans ih p.conv

/-- Conversion is exactly common-reduct joinability, not semantic equality. -/
theorem conv_iff_join : Conv a b ↔ ∃ c, Red a c ∧ Red b c :=
  ⟨Conv.join, fun ⟨_, ha, hb⟩ => .trans ha.conv hb.conv.symm⟩

/-- Reduction of a term-function type keeps its outer constructor. -/
theorem Red.arr_inv {a b c : Ty Δ .star} (h : Red (.arr a b) c) :
    ∃ a' b', c = .arr a' b' ∧ Red a a' ∧ Red b b' := by
  induction h with
  | refl => exact ⟨a, b, rfl, .refl, .refl⟩
  | tail h p ih =>
    obtain ⟨a', b', rfl, ha, hb⟩ := ih
    cases p with
    | arr pa pb => exact ⟨_, _, rfl, ha.tail pa, hb.tail pb⟩

/-- Reduction of a quantified type keeps its binder kind and outer shape. -/
theorem Red.all_inv {body : Ty (μ :: Δ) .star} {c : Ty Δ .star}
    (h : Red (.all body) c) :
    ∃ body' : Ty (μ :: Δ) .star, c = .all body' ∧ Red body body' := by
  induction h with
  | refl => exact ⟨body, rfl, .refl⟩
  | tail h p ih =>
    obtain ⟨body', rfl, hb⟩ := ih
    cases p with
    | all pb => exact ⟨_, rfl, hb.tail pb⟩

/-- Convertible term-function types have convertible domains and codomains. -/
theorem Conv.arr_inj {a a' b b' : Ty Δ .star}
    (h : Conv (.arr a b) (.arr a' b')) : Conv a a' ∧ Conv b b' := by
  obtain ⟨c, hc, hc'⟩ := h.join
  obtain ⟨x, y, hxy, hx, hy⟩ := hc.arr_inv
  obtain ⟨x', y', hxy', hx', hy'⟩ := hc'.arr_inv
  obtain ⟨rfl, rfl⟩ := Ty.arr.inj (hxy.symm.trans hxy')
  exact ⟨.trans hx.conv hx'.conv.symm, .trans hy.conv hy'.conv.symm⟩

/-- Conversion cannot change the kind of a universal binder. -/
theorem Conv.all_kind {ν : Kind} {body : Ty (μ :: Δ) .star}
    {body' : Ty (ν :: Δ) .star} (h : Conv (.all body) (.all body')) :
    μ = ν := by
  obtain ⟨c, hc, hc'⟩ := h.join
  obtain ⟨b, hb, _⟩ := hc.all_inv
  obtain ⟨b', hb', _⟩ := hc'.all_inv
  exact (Ty.all.inj (hb.symm.trans hb')).1

/-- Convertible quantified types at the same kind have convertible bodies. -/
theorem Conv.all_inj {body body' : Ty (μ :: Δ) .star}
    (h : Conv (.all body) (.all body')) : Conv body body' := by
  obtain ⟨c, hc, hc'⟩ := h.join
  obtain ⟨b, hb, hr⟩ := hc.all_inv
  obtain ⟨b', hb', hr'⟩ := hc'.all_inv
  have e : b = b' := eq_of_heq (Ty.all.inj (hb.symm.trans hb')).2
  subst b'
  exact .trans hr.conv hr'.conv.symm

end Cslib.Languages.LambdaCalculus.FOmega.Ty
