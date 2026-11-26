/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean` and
`Definitions/Def_CerednikDrinfeld_GradedCartierNModule.lean`
(every declaration except `isBaseChangeAlong'_iff`,
`IsBaseChangeAlong'.map_teichmullerAct` and
`IsBaseChangeAlong.map_teichmullerAct`, which are additions here;
`IsBaseChangeAlong'` adds the clause `j' = φ.comp j`).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData

/-!
# The graded `N`-module of a graded Cartier module

From graded Cartier module data `D` we build the Frobenius-twisted module
`Sigma`, the relation submodule identifying Verschiebung with the
uniformizer, the quotient `NMod`, the map `lambda` to `M`, the Lie quotient
`M / V M`, and the notions of Cartier and canonical `L`-maps.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura :
  les théorèmes de Čerednik et de Drinfeld*, Astérisque 196–197 (1991), 45–158.
  Chapter II: §3.2 defines the quotient `N(M)` of `M ⊕ M^σ` by the pairs
  `(V m, -Π m)`, §3.3 the map `λ`, and Proposition 3.8 the maps `L_M`, the one
  family of maps `M → N(M)` with `λ ∘ L_M = F` that commutes with base change.
  `IsCanonicalLMap` asks instead for a commuting square with a Cartier `L`-map
  over a `p`-torsion-free ring, as in part (c) of that proof, through the maps
  of `IsBaseChangeAlong'` rather than base change, and `cartierL` chooses a map
  that satisfies it; neither uniqueness nor compatibility with base change is
  proved here.
-/

@[expose] public section

universe u v

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData.{u, v} p j)

/-- **Frobenius twist.** The additive group of `M` with the action of
`WittVector p B` precomposed with its Frobenius `σ`: `w` acts as `σ w`. -/
noncomputable def Sigma (D : GradedCartierModuleData p j) : Type v :=
  D.M

noncomputable instance : AddCommGroup D.Sigma :=
  inferInstanceAs (AddCommGroup D.M)

noncomputable instance : Module (WittVector p B) D.Sigma :=
  Module.compHom D.M (WittVector.frobenius : WittVector p B →+* WittVector p B)

/-- **Into the Frobenius twist.** The identity map from `M` to its Frobenius
twist, as an additive equivalence. -/
noncomputable def toSigma : D.M ≃+ D.Sigma :=
  AddEquiv.refl _

/-- **Out of the Frobenius twist.** The identity map from the Frobenius twist
back to `M`, as an additive equivalence. -/
noncomputable def ofSigma : D.Sigma ≃+ D.M :=
  AddEquiv.refl _

@[simp] theorem ofSigma_toSigma (m : D.M) : D.ofSigma (D.toSigma m) = m :=
  rfl

@[simp] theorem toSigma_ofSigma (m : D.Sigma) : D.toSigma (D.ofSigma m) = m :=
  rfl

theorem smul_toSigma (w : WittVector p B) (m : D.M) :
    w • D.toSigma m = D.toSigma (WittVector.frobenius w • m) :=
  rfl

theorem ofSigma_smul (w : WittVector p B) (m : D.Sigma) :
    D.ofSigma (w • m) = WittVector.frobenius w • D.ofSigma m :=
  rfl

/-- **Relation map.** The `WittVector p B`-linear map from the Frobenius twist
to `M × Sigma` sending `m` to `(V m, -ϖ m)`; its range is `nRel`. -/
noncomputable def nRelMap : D.Sigma →ₗ[WittVector p B] D.M × D.Sigma where
  toFun m := (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
  map_add' m m' := by
    simp only [map_add, map_neg, neg_add, Prod.mk_add_mk]
  map_smul' w m := by
    change (D.verschiebung (D.ofSigma (w • m)),
        D.toSigma (-D.varpi (D.ofSigma (w • m)))) =
      w • (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
    rw [Prod.smul_mk, ofSigma_smul, D.varpi_smul, D.smul_verschiebung,
      smul_toSigma, smul_neg]

@[simp] theorem nRelMap_apply (m : D.Sigma) :
    D.nRelMap m =
      (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m))) :=
  rfl

/-- **Relation submodule.** The submodule of `M × Sigma` of the pairs
`(V m, -ϖ m)`, the range of `nRelMap`. -/
noncomputable def nRel : Submodule (WittVector p B) (D.M × D.Sigma) :=
  LinearMap.range D.nRelMap

/-- **Graded `N`-module.** `M × Sigma` modulo the relation submodule: the
class of `(V m, -ϖ m)` is zero for every `m` (`nMk_verschiebung_neg_varpi`). -/
abbrev NMod : Type v :=
  (D.M × D.Sigma) ⧸ D.nRel

/-- **Classes in the `N`-module.** The additive map sending `(m, m')`, a pair
of elements of `M`, to the class of `(m, m')`, with `m'` read in the Frobenius
twist. -/
noncomputable def nMk : D.M × D.M →+ D.NMod :=
  (D.nRel.mkQ.toAddMonoidHom).comp
    (AddMonoidHom.prodMap (AddMonoidHom.id D.M) D.toSigma.toAddMonoidHom)

theorem nMk_apply (m m' : D.M) :
    D.nMk (m, m') = D.nRel.mkQ (m, D.toSigma m') :=
  rfl

theorem nMk_surjective : Function.Surjective D.nMk := by
  intro z
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nRel.mkQ_surjective z
  exact ⟨(m, D.ofSigma m'), rfl⟩

theorem nMk_verschiebung_neg_varpi (m : D.M) :
    D.nMk (D.verschiebung m, -D.varpi m) = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨D.toSigma m, rfl⟩

theorem smul_nMk (w : WittVector p B) (m m' : D.M) :
    w • D.nMk (m, m') = D.nMk (w • m, WittVector.frobenius w • m') :=
  rfl

/-- **The map `lambda`.** The `WittVector p B`-linear map from the `N`-module
to `M` sending the class of `(m, m')` to `ϖ m + V m'` (`lambda_nMk`); it
vanishes on the relations because `ϖ` commutes with `V`. -/
noncomputable def lambda : D.NMod →ₗ[WittVector p B] D.M :=
  D.nRel.liftQ
    { toFun := fun x => D.varpi x.1 + D.verschiebung (D.ofSigma x.2)
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := fun w x => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ofSigma_smul,
          RingHom.id_apply, smul_add, D.smul_verschiebung] }
    (by
      rintro x ⟨m, rfl⟩
      change D.varpi (D.verschiebung (D.ofSigma m)) +
        D.verschiebung (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m)))) = 0
      rw [ofSigma_toSigma, map_neg, D.varpi_verschiebung, add_neg_cancel])

@[simp] theorem lambda_nMk (m m' : D.M) :
    D.lambda (D.nMk (m, m')) = D.varpi m + D.verschiebung m' :=
  rfl

/-- **Image of Verschiebung.** The image `V M` of Verschiebung, as a
`WittVector p B`-submodule of `M`. -/
noncomputable def vRange : Submodule (WittVector p B) D.M where
  carrier := Set.range D.verschiebung
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨x, rfl⟩
    exact ⟨WittVector.frobenius w • x, (D.smul_verschiebung w x).symm⟩

theorem mem_vRange_iff (x : D.M) :
    x ∈ D.vRange ↔ ∃ y, D.verschiebung y = x :=
  Iff.rfl

/-- **Lie quotient.** The quotient `M / V M`. -/
abbrev LieQuot : Type v :=
  D.M ⧸ D.vRange

/-- **Projection to the Lie quotient.** The `WittVector p B`-linear map from
the `N`-module to `M / V M` sending the class of `(m, m')` to the class of
`m`. -/
noncomputable def toLieQuot : D.NMod →ₗ[WittVector p B] D.LieQuot :=
  D.nRel.liftQ (D.vRange.mkQ.comp (LinearMap.fst _ _ _)) (by
    rintro x ⟨m, rfl⟩
    change D.vRange.mkQ (D.verschiebung (D.ofSigma m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨D.ofSigma m, rfl⟩)

/-- **Map from the Frobenius twist.** The `WittVector p B`-linear map from the
Frobenius twist to the `N`-module sending `m'` to the class of `(0, m')`. It
need not be injective: it sends `ϖ m` to zero whenever `V m = 0`. -/
noncomputable def inrSigma : D.Sigma →ₗ[WittVector p B] D.NMod :=
  D.nRel.mkQ.comp (LinearMap.inr _ _ _)

/-- **The uniformizer on the `N`-module.** The `WittVector p B`-linear map
sending the class of `(m, m')` to the class of `(ϖ m, ϖ m')`. -/
noncomputable def nVarpi : D.NMod →ₗ[WittVector p B] D.NMod :=
  D.nRel.mapQ D.nRel
    (LinearMap.prodMap D.varpi
      { toFun := fun m => D.toSigma (D.varpi (D.ofSigma m))
        map_add' := fun x y => by simp only [map_add]
        map_smul' := fun w m => by
          rw [ofSigma_smul, map_smul, RingHom.id_apply, smul_toSigma] })
    (by
      rintro x ⟨m, rfl⟩
      refine ⟨D.toSigma (D.varpi (D.ofSigma m)), ?_⟩
      change (D.verschiebung (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))),
          D.toSigma (-D.varpi
            (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))))) =
        (D.varpi (D.verschiebung (D.ofSigma m)),
          D.toSigma (D.varpi
            (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
      simp only [ofSigma_toSigma, D.varpi_verschiebung, map_neg])

/-- **Graded pieces of the `N`-module.** The image of `piece i × piece i`
under `nMk`. -/
noncomputable def nPiece (i : Fin 2) : AddSubgroup D.NMod :=
  (((D.piece i).toAddSubgroup).prod ((D.piece i).toAddSubgroup)).map D.nMk

/-- **Induced map of `N`-modules.** For data `D'` over a ring `B'` and an
additive map `f : D.M →+ D'.M` that commutes with `V` and `ϖ`, the additive map
from the `N`-module of `D` to that of `D'` sending the class of `(m, m')` to the
class of `(f m, f m')` (`nMap_nMk`). -/
noncomputable def nMap {B' : Type u} [CommRing B'] {j' : Zp2 p →+* B'}
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) : D.NMod →+ D'.NMod :=
  QuotientAddGroup.map D.nRel.toAddSubgroup D'.nRel.toAddSubgroup
    (AddMonoidHom.prodMap f
      (D'.toSigma.toAddMonoidHom.comp (f.comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    refine ⟨D'.toSigma (f (D.ofSigma m)), ?_⟩
    change (D'.verschiebung (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))),
        D'.toSigma (-D'.varpi
          (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))))) =
      (f (D.verschiebung (D.ofSigma m)),
        D'.toSigma (f (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
    simp only [ofSigma_toSigma, hV, map_neg, hPi])

theorem nMap_nMk {B' : Type u} [CommRing B'] {j' : Zp2 p →+* B'}
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (m m' : D.M) :
    D.nMap D' f hV hPi (D.nMk (m, m')) = D'.nMk (f m, f m') :=
  rfl

/-- **Basis-preserving semilinear map along a ring map, any target coefficient map.** For
`φ : B →+* B'`, data `D` over `B` with coefficient map `j`, data `D'` over `B'`
with a coefficient map `j'`, and an additive map `f : D.M →+ D'.M`:
`j' = φ.comp j`, and `f` satisfies the clauses of `IsBaseChangeAlong`. Like
`IsBaseChangeAlong`, this is weaker than base change along `φ`, the completed
extension of scalars. The equation is about the coefficient maps alone; with
the clause on pieces it makes `f` intertwine the Teichmüller actions
(`IsBaseChangeAlong'.map_teichmullerAct`). -/
def IsBaseChangeAlong' {B' : Type u} [CommRing B'] {j' : Zp2 p →+* B'}
    (φ : B →+* B') (D : GradedCartierModuleData p j)
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M) : Prop :=
  j' = φ.comp j ∧
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧
    D'.IsHomogeneousVBasis (fun i => f (γ i)))

theorem isBaseChangeAlong'_iff {B' : Type u} [CommRing B'] (φ : B →+* B')
    (D : GradedCartierModuleData p j)
    (D' : GradedCartierModuleData p (φ.comp j)) (f : D.M →+ D'.M) :
    IsBaseChangeAlong' φ D D' f ↔ IsBaseChangeAlong φ D D' f :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- **Intertwining the Teichmüller actions.** A map `f` with
`IsBaseChangeAlong' φ D D' f` satisfies
`f (D.teichmullerAct c x) = D'.teichmullerAct c (f x)`, for the actions that the
pieces and the coefficient maps `j` and `j' = φ.comp j` determine. -/
theorem IsBaseChangeAlong'.map_teichmullerAct {B' : Type u} [CommRing B']
    {j' : Zp2 p →+* B'} {φ : B →+* B'} {D : GradedCartierModuleData p j}
    {D' : GradedCartierModuleData p j'} {f : D.M →+ D'.M}
    (h : IsBaseChangeAlong' φ D D' f) (c : GaloisField p 2) (x : D.M) :
    f (D.teichmullerAct c x) = D'.teichmullerAct c (f x) := by
  obtain ⟨rfl, hsmul, -, -, -, hpiece, -⟩ := h
  have key : ∀ (i : Fin 2) (y : D.M), y ∈ D.piece i →
      f (D.teichmullerAct c y) = D'.teichmullerAct c (f y) := by
    intro i y hy
    rw [D.teichmullerAct_of_mem c hy, D'.teichmullerAct_of_mem c (hpiece i y hy),
      homothety_apply, homothety_apply, hsmul, WittVector.map_teichmuller, map_pow,
      RingHom.comp_apply]
  rw [← Submodule.projection_add_projection_eq_self D.isCompl_piece x, map_add, map_add,
    map_add, map_add, key 0 _ (Submodule.projection_apply_mem _ _),
    key 1 _ (Submodule.projection_apply_mem _ _)]

theorem IsBaseChangeAlong.map_teichmullerAct {B' : Type u} [CommRing B']
    {φ : B →+* B'} {D : GradedCartierModuleData p j}
    {D' : GradedCartierModuleData p (φ.comp j)} {f : D.M →+ D'.M}
    (h : IsBaseChangeAlong φ D D' f) (c : GaloisField p 2) (x : D.M) :
    f (D.teichmullerAct c x) = D'.teichmullerAct c (f x) :=
  ((isBaseChangeAlong'_iff φ D D' f).mpr h).map_teichmullerAct c x

/-- **Cartier `L`-map.** An additive map `L` from `M` to the `N`-module such
that, for all `w` and `x`, `L (w • x) = σ w • L x` with `σ` the Frobenius of
`WittVector p B`, `L (V x)` is the class of `(ϖ x, 0)`, and
`lambda (L x) = F x`. -/
structure IsCartierLMap (L : D.M →+ D.NMod) : Prop where
  /-- `L` is Frobenius-semilinear. -/
  map_smul : ∀ (w : WittVector p B) (x : D.M),
    L (w • x) = WittVector.frobenius w • L x
  /-- `L (V x)` is the class of `(ϖ x, 0)`. -/
  map_verschiebung : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)
  /-- `lambda` after `L` is Frobenius. -/
  lambda_comp : ∀ x : D.M, D.lambda (L x) = D.frobenius x

/-- **Canonical `L`-map.** A Cartier `L`-map `L` on `D`, over `B` with
coefficient map `j`, that forms a commuting square with a Cartier `L`-map over a
`p`-torsion-free ring mapping onto `B`. That is, there are a commutative ring
`S` on which multiplication by `p` is injective, a ring map `jS : Zp2 p →+* S`,
a surjective ring map `φ : S →+* B`, a special Cartier module `Dl` over `S`
with coefficient map `jS`, an additive map `f : Dl.M →+ D.M` with
`IsBaseChangeAlong' φ Dl D f` (so `j = φ.comp jS`), and a Cartier `L`-map `Ll`
on `Dl`, such that `L (f x) = nMap f (Ll x)` for every `x` in `Dl.M`, where
`nMap f` is the map of `N`-modules that `f` induces. The map `f` is a
basis-preserving semilinear map along `φ`, not necessarily the base change of
`Dl` along `φ`. A special Cartier module over such an `S` is not enough: `L`
itself must satisfy this equation. -/
structure IsCanonicalLMap (L : D.M →+ D.NMod) : Prop where
  /-- The map is a Cartier `L`-map. -/
  isCartierLMap : D.IsCartierLMap L
  /-- `L` forms a commuting square with a Cartier `L`-map `Ll` on a special
  Cartier module `Dl` over a `p`-torsion-free ring `S` with a surjection
  `φ : S →+* B`, through a map `f : Dl.M →+ D.M` with
  `IsBaseChangeAlong' φ Dl D f` (so `j = φ.comp jS`): `L (f x) = nMap f (Ll x)`
  for every `x`. -/
  exists_lift : ∃ (S : Type u) (_ : CommRing S) (jS : Zp2 p →+* S) (φ : S →+* B)
    (_ : Function.Surjective φ) (_ : ∀ s : S, (p : S) * s = 0 → s = 0)
    (Dl : GradedCartierModuleData.{u, v} p jS) (_ : Dl.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong' φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (_ : Dl.IsCartierLMap Ll),
    ∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.2.1 hf.2.2.2.2.1 (Ll x)

/-- **Chosen canonical `L`-map.** A canonical `L`-map, chosen from a proof that
one exists. In Boutot–Carayol (Proposition 3.8 of Chapter II) the maps `L_M`
form the one family with `λ ∘ L_M = F` that commutes with base change; neither
property is proved here, and `cartierL` is an unspecified canonical `L`-map. -/
noncomputable def cartierL (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.M →+ D.NMod :=
  h.choose

theorem cartierL_spec (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) :
    D.IsCanonicalLMap (D.cartierL h) :=
  h.choose_spec

/-- **The operator `phi`.** For an additive map `L` from `M` to the `N`-module
with `L (V x)` the class of `(ϖ x, 0)`, the additive endomorphism of the
`N`-module sending the class of `(x, x')` to `L x` plus the class of `(x', 0)`
(`phi_nMk`). -/
noncomputable def phi (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.NMod →+ D.NMod :=
  QuotientAddGroup.lift D.nRel.toAddSubgroup
    (AddMonoidHom.coprod L
      (D.nMk.comp ((AddMonoidHom.inl D.M D.M).comp
        D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    change L (D.verschiebung (D.ofSigma m)) +
      D.nMk (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))), 0) = 0
    rw [hL, ofSigma_toSigma, ← map_add, Prod.mk_add_mk, add_neg_cancel,
      add_zero]
    exact map_zero D.nMk)

theorem phi_nMk (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (x x' : D.M) :
    D.phi L hL (D.nMk (x, x')) = L x + D.nMk (x', 0) :=
  rfl

/-- **Fixed points of `phi`.** The additive subgroup `eta` of the `N`-module
of the `z` with `phi z = z` (`mem_eta_iff`). -/
noncomputable def eta (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    AddSubgroup D.NMod :=
  (D.phi L hL - AddMonoidHom.id D.NMod).ker

theorem mem_eta_iff (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (z : D.NMod) :
    z ∈ D.eta L hL ↔ D.phi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
  rfl

/-- **Intersection of `eta` with a graded piece of `N`.** The intersection of
`eta` with `nPiece i`, the `i`-th graded piece of the `N`-module. These
intersections need not decompose `eta`. -/
noncomputable def etaPiece (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (i : Fin 2) : AddSubgroup D.NMod :=
  D.eta L hL ⊓ D.nPiece i

/-- **From `eta` to the Lie quotient.** The restriction to `eta` of the
projection from the `N`-module to `M / V M`. -/
noncomputable def u (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.eta L hL →+ D.LieQuot :=
  D.toLieQuot.toAddMonoidHom.comp (D.eta L hL).subtype

end GradedCartierModuleData

end CerednikDrinfeld
