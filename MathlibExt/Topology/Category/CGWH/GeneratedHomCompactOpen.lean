/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.GeneratedHom
public import Mathlib.Topology.Convenient.HomSpace

/-!
# Generated and compact-open mapping topologies

For a CGWH source in the same universe as its compact Hausdorff probes, an
explicit Hausdorff hypothesis identifies the compact-Hausdorff-generated
mapping topology with Mathlib's compact-open topology.
-/

@[expose] public section

set_option autoImplicit false

open Set Topology

universe v

namespace CGWH

/-- For a Hausdorff CGWH source in the probe universe, the generated mapping
topology agrees with the compact-open topology. -/
def generatedMapHomeomorphCompactOpenOfT2
    (A B : CGWH.{v, v}) [T2Space A] :
    ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{v} A B ≃ₜ
      C(A, B) where
  toEquiv := generatedMapEquivContinuousMap A B
  continuous_toFun := by
    rw [ContinuousMap.continuous_compactOpen]
    intro K hK U hU
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let Kc : CompHaus.{v} := CompHaus.of K
    let inc : C(CompactlyGenerated.compactHausProbes Kc, A) :=
      ContinuousMap.subtypeVal K
    let precomp := ContinuousMapGeneratedBy.precomp (T := B) inc
    have hprecomp : Continuous precomp :=
      ContinuousMapGeneratedBy.continuous_precomp inc
    have hopen : IsOpen
        {g : C(CompactlyGenerated.compactHausProbes Kc, B) |
          Set.range g ⊆ U} :=
      ContinuousMap.isOpen_setOfPred_range_subset hU
    have heq :
        {g : ContinuousMapGeneratedBy
            CompactlyGenerated.compactHausProbes.{v} A B |
          MapsTo (generatedMapEquivContinuousMap A B g) K U} =
          precomp ⁻¹' {g | Set.range g ⊆ U} := by
      ext g
      constructor
      · intro hg y hy
        rcases hy with ⟨x, rfl⟩
        exact hg x.property
      · intro hg x hx
        exact hg ⟨⟨x, hx⟩, rfl⟩
    change IsOpen
      {g | MapsTo (generatedMapEquivContinuousMap A B g) K U}
    rw [heq]
    exact hopen.preimage hprecomp
  continuous_invFun := by
    rw [ContinuousMapGeneratedBy.continuous_iff]
    intro K p
    have h := ContinuousMap.continuous_precomp (Z := B) p
    convert h using 1
    funext g
    apply ContinuousMap.ext
    intro a
    rfl

@[simp]
theorem generatedMapHomeomorphCompactOpenOfT2_apply
    (A B : CGWH.{v, v}) [T2Space A]
    (f : ContinuousMapGeneratedBy
      CompactlyGenerated.compactHausProbes.{v} A B)
    (a : A) :
    generatedMapHomeomorphCompactOpenOfT2 A B f a = f a :=
  rfl

/- The historical name uses the builtin persistent export mechanism.
The scoped rename preserves the same public definition and its type. -/
open CGWH renaming generatedMapHomeomorphCompactOpenOfT2 →
  generatedMapHomeomorphCompactOpen_of_t2 in
export _root_ (generatedMapHomeomorphCompactOpen_of_t2)

/-- The historical homeomorphism retains its original application formula. -/
@[simp]
public theorem generatedMapHomeomorphCompactOpen_of_t2_apply
    (A B : CGWH.{v, v}) [T2Space A]
    (f : ContinuousMapGeneratedBy
      CompactlyGenerated.compactHausProbes.{v} A B)
    (a : A) :
    generatedMapHomeomorphCompactOpen_of_t2 A B f a = f a :=
  generatedMapHomeomorphCompactOpenOfT2_apply A B f a

end CGWH
