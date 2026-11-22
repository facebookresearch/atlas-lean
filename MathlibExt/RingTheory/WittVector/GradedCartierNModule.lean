/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean` and
`Definitions/Def_CerednikDrinfeld_GradedCartierNModule.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData

/-!
# The graded `N`-module of a graded Cartier module

From graded Cartier module data `D` we build the Frobenius-twisted module
`Sigma`, the relation submodule identifying Verschiebung with the
uniformizer, the quotient `NMod`, the map `lambda` to `M`, the Lie quotient
`M / V M`, and the notions of Cartier and canonical `L`-maps.
-/

@[expose] public section

universe u v

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData.{u, v} p j)

/-- The Frobenius twist of `M`: the same additive group with the Witt
action precomposed with Frobenius. -/
noncomputable def Sigma (D : GradedCartierModuleData p j) : Type v :=
  D.M

noncomputable instance : AddCommGroup D.Sigma :=
  inferInstanceAs (AddCommGroup D.M)

noncomputable instance : Module (WittVector p B) D.Sigma :=
  Module.compHom D.M (WittVector.frobenius : WittVector p B →+* WittVector p B)

/-- The identity map from `M` to its Frobenius twist. -/
noncomputable def toSigma : D.M ≃+ D.Sigma :=
  AddEquiv.refl _

/-- The identity map from the Frobenius twist back to `M`. -/
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

/-- The relation map whose range identifies `(V x, -varpi x)` with zero. -/
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

/-- The relation submodule of `M × Sigma`. -/
noncomputable def nRel : Submodule (WittVector p B) (D.M × D.Sigma) :=
  LinearMap.range D.nRelMap

/-- The graded `N`-module: `(M × Sigma)` modulo the relation submodule. -/
abbrev NMod : Type v :=
  (D.M × D.Sigma) ⧸ D.nRel

/-- The quotient map from pairs of elements of `M` to the `N`-module. -/
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

/-- The map `lambda : NMod → M` given by `varpi` on the first factor and
Verschiebung on the second. -/
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

/-- The range of Verschiebung as a submodule. -/
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

/-- The Lie quotient `M / V M`. -/
abbrev LieQuot : Type v :=
  D.M ⧸ D.vRange

/-- The projection from the `N`-module to the Lie quotient. -/
noncomputable def toLieQuot : D.NMod →ₗ[WittVector p B] D.LieQuot :=
  D.nRel.liftQ (D.vRange.mkQ.comp (LinearMap.fst _ _ _)) (by
    rintro x ⟨m, rfl⟩
    change D.vRange.mkQ (D.verschiebung (D.ofSigma m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨D.ofSigma m, rfl⟩)

/-- The inclusion of the Frobenius twist into the `N`-module. -/
noncomputable def inrSigma : D.Sigma →ₗ[WittVector p B] D.NMod :=
  D.nRel.mkQ.comp (LinearMap.inr _ _ _)

/-- The uniformizer acting on the `N`-module. -/
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
      show (D.verschiebung (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))),
          D.toSigma (-D.varpi
            (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))))) =
        (D.varpi (D.verschiebung (D.ofSigma m)),
          D.toSigma (D.varpi
            (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
      simp only [ofSigma_toSigma, D.varpi_verschiebung, map_neg])

/-- The graded pieces of the `N`-module. -/
noncomputable def nPiece (i : Fin 2) : AddSubgroup D.NMod :=
  (((D.piece i).toAddSubgroup).prod ((D.piece i).toAddSubgroup)).map D.nMk

/-- The map on `N`-modules induced by a map of graded Cartier module data
compatible with Verschiebung and the uniformizer. -/
noncomputable def nMap {B' : Type u} [CommRing B'] {j' : Zp2 p →+* B'}
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) : D.NMod →+ D'.NMod :=
  QuotientAddGroup.map D.nRel.toAddSubgroup D'.nRel.toAddSubgroup
    (AddMonoidHom.prodMap f
      (D'.toSigma.toAddMonoidHom.comp (f.comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    refine ⟨D'.toSigma (f (D.ofSigma m)), ?_⟩
    show (D'.verschiebung (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))),
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

/-- Base change of graded Cartier module data, stated with the target ring
map `j'` implicit. -/
def IsBaseChangeAlong' {B' : Type u} [CommRing B'] {j' : Zp2 p →+* B'}
    (φ : B →+* B') (D : GradedCartierModuleData p j)
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧
    D'.IsHomogeneousVBasis (fun i => f (γ i)))

/-- A Cartier `L`-map: a Frobenius-semilinear map to the `N`-module that
sends Verschiebung to the uniformizer and lifts Frobenius through
`lambda`. -/
structure IsCartierLMap (L : D.M →+ D.NMod) : Prop where
  /-- `L` is Frobenius-semilinear. -/
  map_smul : ∀ (w : WittVector p B) (x : D.M),
    L (w • x) = WittVector.frobenius w • L x
  /-- `L` sends Verschiebung to the uniformizer term. -/
  map_verschiebung : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)
  /-- `lambda` after `L` is Frobenius. -/
  lambda_comp : ∀ x : D.M, D.lambda (L x) = D.frobenius x

/-- A canonical `L`-map: a Cartier `L`-map that lifts from a special
Cartier module over a `p`-torsion-free base change. -/
structure IsCanonicalLMap (L : D.M →+ D.NMod) : Prop where
  /-- The map is a Cartier `L`-map. -/
  isCartierLMap : D.IsCartierLMap L
  /-- The map lifts from a special Cartier module over a surjectively
  `p`-torsion-free presented base. -/
  exists_lift : ∃ (S : Type u) (_ : CommRing S) (jS : Zp2 p →+* S) (φ : S →+* B)
    (_ : Function.Surjective φ) (_ : ∀ s : S, (p : S) * s = 0 → s = 0)
    (Dl : GradedCartierModuleData.{u, v} p jS) (_ : Dl.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong' φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (_ : Dl.IsCartierLMap Ll),
    ∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)

/-- The canonical `L`-map chosen from a proof of its existence. -/
noncomputable def cartierL (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.M →+ D.NMod :=
  h.choose

theorem cartierL_spec (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) :
    D.IsCanonicalLMap (D.cartierL h) :=
  h.choose_spec

/-- The operator `phi` on the `N`-module built from an `L`-map. -/
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

/-- The subgroup `eta` of fixed points of `phi`. -/
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

/-- The graded pieces of `eta`. -/
noncomputable def etaPiece (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (i : Fin 2) : AddSubgroup D.NMod :=
  D.eta L hL ⊓ D.nPiece i

/-- The map from `eta` to the Lie quotient. -/
noncomputable def u (L : D.M →+ D.NMod)
    (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.eta L hL →+ D.LieQuot :=
  D.toLieQuot.toAddMonoidHom.comp (D.eta L hL).subtype

end GradedCartierModuleData

end CerednikDrinfeld
