/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import MathlibExt.Topology.Homotopy.PathReparametrization

/-!
# Changing the basepoint of a topological loop space

A path p from x to y induces the continuous conjugation map sending a loop
gamma at x to p inverse, then gamma, then p.  Concatenation with p inverse
gives an inverse up to homotopy.

The inverse laws below are genuine continuous-map homotopies on the whole
loop spaces.  They are built from uniform path reparameterizations and do not
promote merely pointwise path homotopies.

No strict-loop factorization, singular comparison, homotopy-group shift,
weak-equivalence, spectrum, or Q/S comparison is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open unitInterval
open scoped Topology ContinuousMap

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private def loopPostTransMap {a b : X} (p : Path a b) (z : X) :
    C(Path z a, Path z b) where
  toFun q := q.trans p
  continuous_toFun := by fun_prop

private def loopPostAssocLeft {a b c : X} (p : Path a b)
    (r : Path b c) (z : X) : C(Path z a, Path z c) where
  toFun q := (q.trans p).trans r
  continuous_toFun := by fun_prop

private def loopPostAssocRight {a b c : X} (p : Path a b)
    (r : Path b c) (z : X) : C(Path z a, Path z c) where
  toFun q := q.trans (p.trans r)
  continuous_toFun := by fun_prop

private def loopAssocReparam : I → I := fun t =>
  ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩

private theorem loopAssocReparam_continuous :
    Continuous (loopAssocReparam : I → I) := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transAssocReparamAux

private theorem loopAssocReparam_zero : loopAssocReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_zero

private theorem loopAssocReparam_one : loopAssocReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_one

private def loopPostAssocMapHomotopy {a b c : X} (p : Path a b)
    (r : Path b c) (z : X) :
    (loopPostAssocLeft p r z).Homotopy (loopPostAssocRight p r z) := by
  let H := (pathReparamMapHomotopy (a := z) (b := c) loopAssocReparam
    loopAssocReparam_continuous loopAssocReparam_zero
      loopAssocReparam_one).compContinuousMap (loopPostAssocRight p r z)
  have hsource :
      (pathReparamMap loopAssocReparam loopAssocReparam_continuous
          loopAssocReparam_zero loopAssocReparam_one).comp
          (loopPostAssocRight p r z) =
        loopPostAssocLeft p r z := by
    apply ContinuousMap.ext
    intro q
    exact (Path.Homotopy.trans_assoc_reparam q p r).symm
  exact H.cast hsource rfl

private def loopPathHomotopyFamily {a b : X} {p q : Path a b}
    (H : p.Homotopy q) : C(I, Path a b) where
  toFun := H.eval
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact H.continuous_toFun

private def loopRightHcompMapHomotopy {a b : X} {p q : Path a b}
    (H : p.Homotopy q) (z : X) :
    (loopPostTransMap p z).Homotopy (loopPostTransMap q z) where
  toFun sq := sq.2.trans (H.eval sq.1)
  map_zero_left gamma := by
    rw [Path.Homotopy.eval_zero]
    rfl
  map_one_left gamma := by
    rw [Path.Homotopy.eval_one]
    rfl
  continuous_toFun := by
    exact Continuous.path_trans continuous_snd
      ((loopPathHomotopyFamily H).continuous.comp continuous_fst)

private def loopTransReflReparam : I → I := fun t =>
  ⟨Path.Homotopy.transReflReparamAux t,
    Path.Homotopy.transReflReparamAux_mem_I t⟩

private theorem loopTransReflReparam_continuous :
    Continuous (loopTransReflReparam : I → I) := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transReflReparamAux

private theorem loopTransReflReparam_zero : loopTransReflReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_zero

private theorem loopTransReflReparam_one : loopTransReflReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_one

private def loopTransReflMapHomotopy (a b : X) :
    (loopPostTransMap (Path.refl b) a).Homotopy
      (ContinuousMap.id (Path a b)) := by
  let H := pathReparamMapHomotopy (a := a) (b := b)
    loopTransReflReparam loopTransReflReparam_continuous
      loopTransReflReparam_zero loopTransReflReparam_one
  have hsource :
      pathReparamMap loopTransReflReparam
          loopTransReflReparam_continuous loopTransReflReparam_zero
          loopTransReflReparam_one =
        loopPostTransMap (Path.refl b) a := by
    apply ContinuousMap.ext
    intro q
    exact (Path.Homotopy.trans_refl_reparam q).symm
  exact H.cast hsource rfl

private def loopPostCancelMapHomotopy {a b : X} (p : Path a b) (z : X) :
    ((loopPostTransMap p.symm z).comp (loopPostTransMap p z)).Homotopy
      (ContinuousMap.id (Path z a)) := by
  have hcancel : (p.trans p.symm).Homotopy (Path.refl a) :=
    (Path.Homotopy.reflTransSymm p).symm
  exact (loopPostAssocMapHomotopy p p.symm z).trans
    ((loopRightHcompMapHomotopy hcancel z).trans
      (loopTransReflMapHomotopy z a))

private def loopPostTransHomotopyEquiv {a b : X} (p : Path a b) (z : X) :
    Path z a ≃ₕ Path z b where
  toFun := loopPostTransMap p z
  invFun := loopPostTransMap p.symm z
  left_inv := ⟨loopPostCancelMapHomotopy p z⟩
  right_inv := by
    exact ⟨by simpa only [Path.symm_symm] using
      loopPostCancelMapHomotopy p.symm z⟩

private def loopPathSymmHomeomorph (a b : X) : Path a b ≃ₜ Path b a where
  toFun := Path.symm
  invFun := Path.symm
  left_inv := Path.symm_symm
  right_inv := Path.symm_symm
  continuous_toFun := Path.continuous_symm
  continuous_invFun := Path.continuous_symm

private def loopPreTransMap {a b : X} (p : Path a b) (z : X) :
    C(Path b z, Path a z) where
  toFun q := p.trans q
  continuous_toFun := by fun_prop

private def loopPreTransHomotopyEquivAux {a b : X} (p : Path a b) (z : X) :
    Path b z ≃ₕ Path a z :=
  ((loopPathSymmHomeomorph b z).toHomotopyEquiv.trans
    (loopPostTransHomotopyEquiv p.symm z)).trans
      (loopPathSymmHomeomorph z a).toHomotopyEquiv

private theorem loopPreTransHomotopyEquivAux_toFun {a b : X}
    (p : Path a b) (z : X) :
    (loopPreTransHomotopyEquivAux p z).toFun = loopPreTransMap p z := by
  apply ContinuousMap.ext
  intro q
  change (q.symm.trans p.symm).symm = p.trans q
  have h := congrArg Path.symm (Path.trans_symm p q)
  simpa only [Path.symm_symm] using h.symm

private theorem loopPreTransHomotopyEquivAux_invFun {a b : X}
    (p : Path a b) (z : X) :
    (loopPreTransHomotopyEquivAux p z).invFun =
      loopPreTransMap p.symm z := by
  apply ContinuousMap.ext
  intro q
  simp only [loopPreTransHomotopyEquivAux,
    ContinuousMap.HomotopyEquiv.trans, loopPathSymmHomeomorph,
    loopPostTransHomotopyEquiv, loopPostTransMap, Path.symm_symm]
  change (q.symm.trans p).symm = p.symm.trans q
  have h := congrArg Path.symm (Path.trans_symm p.symm q)
  simpa only [Path.symm_symm] using h.symm

private def loopPreTransHomotopyEquiv {a b : X} (p : Path a b) (z : X) :
    Path b z ≃ₕ Path a z := by
  let e := loopPreTransHomotopyEquivAux p z
  have hTo : e.toFun = loopPreTransMap p z :=
    loopPreTransHomotopyEquivAux_toFun p z
  have hInv : e.invFun = loopPreTransMap p.symm z :=
    loopPreTransHomotopyEquivAux_invFun p z
  exact
    { toFun := loopPreTransMap p z
      invFun := loopPreTransMap p.symm z
      left_inv := by
        rw [← hTo, ← hInv]
        exact e.left_inv
      right_inv := by
        rw [← hTo, ← hInv]
        exact e.right_inv }

@[simp]
private theorem loopPreTransHomotopyEquiv_apply {a b : X}
    (p : Path a b) (z : X) (q : Path b z) :
    loopPreTransHomotopyEquiv p z q = p.trans q :=
  rfl

@[simp]
private theorem loopPreTransHomotopyEquiv_symm_apply {a b : X}
    (p : Path a b) (z : X) (q : Path a z) :
    (loopPreTransHomotopyEquiv p z).symm q = p.symm.trans q :=
  rfl

private def loopMiddleAssocLeft {a b c d : X} (p : Path a b)
    (r : Path c d) : C(Path b c, Path a d) where
  toFun q := (p.trans q).trans r
  continuous_toFun := by fun_prop

private def loopMiddleAssocRight {a b c d : X} (p : Path a b)
    (r : Path c d) : C(Path b c, Path a d) where
  toFun q := p.trans (q.trans r)
  continuous_toFun := by fun_prop

private def loopMiddleAssocMapHomotopy {a b c d : X} (p : Path a b)
    (r : Path c d) :
    (loopMiddleAssocLeft p r).Homotopy (loopMiddleAssocRight p r) := by
  let H := (pathReparamMapHomotopy (a := a) (b := d) loopAssocReparam
    loopAssocReparam_continuous loopAssocReparam_zero
      loopAssocReparam_one).compContinuousMap (loopMiddleAssocRight p r)
  have hsource :
      (pathReparamMap loopAssocReparam loopAssocReparam_continuous
          loopAssocReparam_zero loopAssocReparam_one).comp
          (loopMiddleAssocRight p r) =
        loopMiddleAssocLeft p r := by
    apply ContinuousMap.ext
    intro q
    exact (Path.Homotopy.trans_assoc_reparam p q r).symm
  exact H.cast hsource rfl

/-- Change the basepoint of a loop along p by conjugation in the order
p inverse, the loop, then p. -/
noncomputable def loopBasepointChange {x y : X} (p : Path x y) :
    C(LoopSpace X x, LoopSpace X y) where
  toFun gamma := p.symm.trans (gamma.trans p)
  continuous_toFun := by fun_prop

/-- Literal conjugation formula for loop basepoint change. -/
@[simp]
theorem loopBasepointChange_apply {x y : X} (p : Path x y)
    (gamma : LoopSpace X x) :
    loopBasepointChange p gamma = p.symm.trans (gamma.trans p) :=
  rfl

private def loopBasepointChangeCore {x y : X} (p : Path x y) :
    LoopSpace X x ≃ₕ LoopSpace X y :=
  (loopPostTransHomotopyEquiv p x).trans
    (loopPreTransHomotopyEquiv p.symm y)

private theorem loopBasepointChangeCore_toFun {x y : X} (p : Path x y) :
    (loopBasepointChangeCore p).toFun = loopBasepointChange p :=
  by
    apply ContinuousMap.ext
    intro gamma
    rfl

private theorem loopBasepointChangeCore_invFun {x y : X} (p : Path x y) :
    (loopBasepointChangeCore p).invFun =
      loopMiddleAssocLeft p p.symm := by
  apply ContinuousMap.ext
  intro q
  change loopPostTransMap p.symm x
      ((loopPreTransHomotopyEquiv p.symm y).symm q) = _
  rw [loopPreTransHomotopyEquiv_symm_apply]
  rw [Path.symm_symm]
  rfl

/-- Changing a loop basepoint along p is a homotopy equivalence whose inverse
is the same construction along p inverse. -/
noncomputable def loopBasepointChangeHomotopyEquiv {x y : X}
    (p : Path x y) : LoopSpace X x ≃ₕ LoopSpace X y := by
  let e := loopBasepointChangeCore p
  let H : e.invFun.Homotopy (loopBasepointChange p.symm) := by
    rw [loopBasepointChangeCore_invFun]
    have htarget : loopMiddleAssocRight p p.symm =
        loopBasepointChange p.symm := by
      apply ContinuousMap.ext
      intro q
      change p.trans (q.trans p.symm) =
        p.symm.symm.trans (q.trans p.symm)
      rw [Path.symm_symm]
    exact (loopMiddleAssocMapHomotopy p p.symm).cast rfl htarget
  exact
    { toFun := loopBasepointChange p
      invFun := loopBasepointChange p.symm
      left_inv := by
        have h := H.symm.compContinuousMap e.toFun
        rw [loopBasepointChangeCore_toFun] at h
        obtain ⟨he⟩ := e.left_inv
        exact ⟨h.trans he⟩
      right_inv := by
        have h := (ContinuousMap.Homotopy.refl e.toFun).comp H
        rw [loopBasepointChangeCore_toFun] at h
        obtain ⟨he⟩ := e.right_inv
        exact ⟨h.symm.trans he⟩ }

/-- The forward map of the basepoint-change homotopy equivalence is the
literal conjugation map. -/
@[simp]
theorem loopBasepointChangeHomotopyEquiv_toFun {x y : X}
    (p : Path x y) :
    (loopBasepointChangeHomotopyEquiv p).toFun = loopBasepointChange p :=
  rfl

/-- The inverse map is literal conjugation along the reversed path. -/
@[simp]
theorem loopBasepointChangeHomotopyEquiv_invFun {x y : X}
    (p : Path x y) :
    (loopBasepointChangeHomotopyEquiv p).invFun =
      loopBasepointChange p.symm :=
  rfl

end ContinuousMap
