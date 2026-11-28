/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupProduct

/-!
# Associativity of tensor-valued continuous cup products

Let R be a commutative ring with a topology, G a profinite group and
A,B,C discrete topological R-representations. The coefficient associator
identifies (A ⊗[R] B) ⊗[R] C with A ⊗[R] (B ⊗[R] C), preserving
the diagonal G-action and discrete topology.

For cocycles, and then for continuous cohomology classes, the products
(x ∪ y) ∪ z and x ∪ (y ∪ z) agree after this coefficient associator
and the identification (p+q)+r=p+(q+r).
The scalar, group and coefficient universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped TensorProduct
universe u v w
namespace ContinuousCohomology
variable {R : Type u} [CommRing R] [TopologicalSpace R] {G : ProfiniteGrp.{v}}

/-- Let R be a commutative ring with a topology, G a profinite group,
and A,B,C topological R-representations with discrete coefficient topologies.
The tensor coefficients have their discrete diagonal G-actions.
The coefficient associator is the continuous equivariant R-linear
isomorphism (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C), with all tensors over R. -/
def discreteTensorCoefficientAssociator
    (A B C : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C] :
    discreteTensorCoefficient (discreteTensorCoefficient A B) C ≅
      discreteTensorCoefficient A (discreteTensorCoefficient B C) where
  hom := TopRep.ofHom
    (ρ := (discreteTensorCoefficient (discreteTensorCoefficient A B) C).ρ)
    (σ := (discreteTensorCoefficient A (discreteTensorCoefficient B C)).ρ)
    { toContinuousLinearMap :=
        (show discreteTensorCoefficient (discreteTensorCoefficient A B) C →L[R]
            discreteTensorCoefficient A (discreteTensorCoefficient B C) from
          { toLinearMap := (TensorProduct.assoc R A B C).toLinearMap
            cont := continuous_of_discreteTopology })
      isIntertwining' h := by
        apply ContinuousLinearMap.ext
        intro z
        change TensorProduct.assoc R A B C
            (TensorProduct.map (TensorProduct.map (A.ρ h).toLinearMap (B.ρ h).toLinearMap)
              (C.ρ h).toLinearMap z) =
          TensorProduct.map (A.ρ h).toLinearMap
            (TensorProduct.map (B.ρ h).toLinearMap (C.ρ h).toLinearMap)
            (TensorProduct.assoc R A B C z)
        exact (TensorProduct.map_map_assoc (A.ρ h).toLinearMap (B.ρ h).toLinearMap
          (C.ρ h).toLinearMap z).symm }
  inv := TopRep.ofHom
    (ρ := (discreteTensorCoefficient A (discreteTensorCoefficient B C)).ρ)
    (σ := (discreteTensorCoefficient (discreteTensorCoefficient A B) C).ρ)
    { toContinuousLinearMap :=
        (show discreteTensorCoefficient A (discreteTensorCoefficient B C) →L[R]
            discreteTensorCoefficient (discreteTensorCoefficient A B) C from
          { toLinearMap := (TensorProduct.assoc R A B C).symm.toLinearMap
            cont := continuous_of_discreteTopology })
      isIntertwining' h := by
        apply ContinuousLinearMap.ext
        intro z
        change (TensorProduct.assoc R A B C).symm
            (TensorProduct.map (A.ρ h).toLinearMap
              (TensorProduct.map (B.ρ h).toLinearMap (C.ρ h).toLinearMap) z) =
          TensorProduct.map (TensorProduct.map (A.ρ h).toLinearMap (B.ρ h).toLinearMap)
            (C.ρ h).toLinearMap ((TensorProduct.assoc R A B C).symm z)
        exact (TensorProduct.map_map_assoc_symm (A.ρ h).toLinearMap (B.ρ h).toLinearMap
          (C.ρ h).toLinearMap z).symm }
  hom_inv_id := by
    ext z
    change (TensorProduct.assoc R A B C).symm (TensorProduct.assoc R A B C z) = z
    exact (TensorProduct.assoc R A B C).symm_apply_apply z
  inv_hom_id := by
    ext z
    change TensorProduct.assoc R A B C ((TensorProduct.assoc R A B C).symm z) = z
    exact (TensorProduct.assoc R A B C).apply_symm_apply z

/-- Let R be a commutative ring with a topology, G a profinite group,
and A,B,C topological R-representations with discrete coefficient topologies.
The tensor coefficients have their discrete diagonal G-actions.
The forward coefficient associator sends (a ⊗ b) ⊗ c to
a ⊗ (b ⊗ c). -/
theorem discreteTensorCoefficientAssociator_hom_tmul
    (A B C : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C] (a : A) (b : B) (c : C) :
    (discreteTensorCoefficientAssociator A B C).hom.hom ((a ⊗ₜ[R] b) ⊗ₜ[R] c) =
      a ⊗ₜ[R] (b ⊗ₜ[R] c) :=
  TensorProduct.assoc_tmul _ _ _

/-- Let R be a commutative ring with a topology, G a profinite group,
and A,B,C topological R-representations with discrete coefficient topologies.
The tensor coefficients have their discrete diagonal G-actions.
The inverse coefficient associator sends a ⊗ (b ⊗ c) to
(a ⊗ b) ⊗ c. -/
theorem discreteTensorCoefficientAssociator_inv_tmul
    (A B C : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C] (a : A) (b : B) (c : C) :
    (discreteTensorCoefficientAssociator A B C).inv.hom (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      (a ⊗ₜ[R] b) ⊗ₜ[R] c :=
  TensorProduct.assoc_symm_tmul _ _ _

private theorem nativePi_degree_transport
    (X : TopRep.{max v w, u, v} R G) (m n : ℕ) (h : m = n) (z : cocycles X m) :
    (eqToHom (congrArg (fun n => continuousCohomology n X) h)).hom (π X m z) =
      π X n ((eqToHom (congrArg (fun n => cocycles X n) h)).hom z) := by
  cases h
  rfl

private theorem nativeCycle_degree_tuple
    (X : TopRep.{max v w, u, v} R G) (m n : ℕ) (h : m = n) (z : cocycles X m)
    (t : Fin (n + 1) → G) :
    resolutionFinUncurry X (n + 1) (((TopRep.homogeneousCochains X).iCycles n
        ((eqToHom (congrArg (fun n => cocycles X n) h)).hom z)).val) t =
      resolutionFinUncurry X (m + 1) (((TopRep.homogeneousCochains X).iCycles m z).val)
        (fun i => t (i.cast (congrArg (fun n => n + 1) h))) := by
  cases h
  rfl

private theorem cup_front_front (p q r : ℕ) (t : Fin (p + (q + r) + 1) → G) :
    homogeneousCupFront p q
        (homogeneousCupFront (p + q) r
          (fun i => t (i.cast (congrArg (fun n => n + 1) (Nat.add_assoc p q r))))) =
      homogeneousCupFront p (q + r) t := by
  funext i
  exact congrArg t (Fin.ext rfl)

private theorem cup_back_front (p q r : ℕ) (t : Fin (p + (q + r) + 1) → G) :
    homogeneousCupBack p q
        (homogeneousCupFront (p + q) r
          (fun i => t (i.cast (congrArg (fun n => n + 1) (Nat.add_assoc p q r))))) =
      homogeneousCupFront q r (homogeneousCupBack p (q + r) t) := by
  funext i
  exact congrArg t (Fin.ext rfl)

private theorem cup_back_back (p q r : ℕ) (t : Fin (p + (q + r) + 1) → G) :
    homogeneousCupBack (p + q) r
        (fun i => t (i.cast (congrArg (fun n => n + 1) (Nat.add_assoc p q r)))) =
      homogeneousCupBack q r (homogeneousCupBack p (q + r) t) := by
  funext i
  exact congrArg t (Fin.ext (Nat.add_assoc p q i.val))

private theorem nativeCycles_ext
    (X : TopRep.{max v w, u, v} R G) (n : ℕ) (z z' : cocycles X n)
    (h : ∀ t : Fin (n + 1) → G,
      resolutionFinUncurry X (n + 1) (((TopRep.homogeneousCochains X).iCycles n z).val) t =
      resolutionFinUncurry X (n + 1) (((TopRep.homogeneousCochains X).iCycles n z').val) t) :
    z = z' := by
  apply (ModuleCat.mono_iff_injective (homogeneousNativeModuleCyclesIso X n).hom).mp inferInstance
  apply (ModuleCat.mono_iff_injective ((flatHomogeneousModuleComplex X).iCycles n)).mp inferInstance
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (homogeneousNativeModuleCyclesIso_tuple_value X n z t).trans
    ((h t).trans (homogeneousNativeModuleCyclesIso_tuple_value X n z' t).symm)

/-- Let R be a commutative ring with a topology, G a profinite group,
and A,B,C topological R-representations with discrete coefficient topologies.
The tensor coefficients have their discrete diagonal G-actions.
For degrees p,q,r ∈ ℕ and cocycles x,y,z in A,B,C, the two
iterated cups agree after applying the coefficient associator to
(x ∪ y) ∪ z and identifying its degree (p+q)+r with p+(q+r). -/
theorem discreteContinuousCupCocycles_assoc
    (A B C : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C]
    (p q r : ℕ) (x : cocycles A p) (y : cocycles B q) (z : cocycles C r) :
    (eqToHom (congrArg (fun n => cocycles
        (discreteTensorCoefficient A (discreteTensorCoefficient B C)) n)
        (Nat.add_assoc p q r))).hom
      (cocyclesMap (X := discreteTensorCoefficient (discreteTensorCoefficient A B) C)
        (Y := discreteTensorCoefficient A (discreteTensorCoefficient B C))
        (ContinuousMonoidHom.id G) (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r)
        (discreteContinuousCupCocycles (discreteTensorCoefficient A B) C (p + q) r
          (discreteContinuousCupCocycles A B p q x y) z)) =
      discreteContinuousCupCocycles A (discreteTensorCoefficient B C) p (q + r) x
        (discreteContinuousCupCocycles B C q r y z) := by
  let L := discreteTensorCoefficient (discreteTensorCoefficient A B) C
  let T := discreteTensorCoefficient A (discreteTensorCoefficient B C)
  let zl := discreteContinuousCupCocycles (discreteTensorCoefficient A B) C (p + q) r
    (discreteContinuousCupCocycles A B p q x y) z
  apply nativeCycles_ext T (p + (q + r))
  intro t
  let tl : Fin ((p + q) + r + 1) → G :=
    fun i => t (i.cast (congrArg (fun n => n + 1) (Nat.add_assoc p q r)))
  let av := resolutionFinUncurry A (p + 1) (((TopRep.homogeneousCochains A).iCycles p x).val)
    (homogeneousCupFront p (q + r) t)
  let bv := resolutionFinUncurry B (q + 1) (((TopRep.homogeneousCochains B).iCycles q y).val)
    (homogeneousCupFront q r (homogeneousCupBack p (q + r) t))
  let cv := resolutionFinUncurry C (r + 1) (((TopRep.homogeneousCochains C).iCycles r z).val)
    (homogeneousCupBack q r (homogeneousCupBack p (q + r) t))
  have hd := nativeCycle_degree_tuple T ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    (cocyclesMap (X := L) (Y := T) (ContinuousMonoidHom.id G)
      (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r) zl) t
  have hm := cocyclesMap_id_tuple_value (discreteTensorCoefficientAssociator A B C).hom
    ((p + q) + r) zl tl
  have ho := discreteContinuousCupCocycles_tuple_value (discreteTensorCoefficient A B) C
    (p + q) r (discreteContinuousCupCocycles A B p q x y) z tl
  have hi := discreteContinuousCupCocycles_tuple_value A B p q x y
    (homogeneousCupFront (p + q) r tl)
  have hvA := congrArg
    (resolutionFinUncurry A (p + 1) (((TopRep.homogeneousCochains A).iCycles p x).val))
    (cup_front_front p q r t)
  have hvB := congrArg
    (resolutionFinUncurry B (q + 1) (((TopRep.homogeneousCochains B).iCycles q y).val))
    (cup_back_front p q r t)
  have hvC := congrArg
    (resolutionFinUncurry C (r + 1) (((TopRep.homogeneousCochains C).iCycles r z).val))
    (cup_back_back p q r t)
  have hl : resolutionFinUncurry L (((p + q) + r) + 1)
      (((TopRep.homogeneousCochains L).iCycles ((p + q) + r) zl).val) tl =
      (av ⊗ₜ[R] bv) ⊗ₜ[R] cv :=
    ho.trans ((congrArg (fun v : discreteTensorCoefficient A B => v ⊗ₜ[R]
        resolutionFinUncurry C (r + 1) (((TopRep.homogeneousCochains C).iCycles r z).val)
          (homogeneousCupBack (p + q) r tl)) hi).trans
      (congrArg₂ (fun ab c => ab ⊗ₜ[R] c) (congrArg₂ (fun a b => a ⊗ₜ[R] b) hvA hvB) hvC))
  have hr₀ := discreteContinuousCupCocycles_tuple_value A (discreteTensorCoefficient B C)
    p (q + r) x (discreteContinuousCupCocycles B C q r y z) t
  have hr₁ := discreteContinuousCupCocycles_tuple_value B C q r y z
    (homogeneousCupBack p (q + r) t)
  have hr : resolutionFinUncurry T (p + (q + r) + 1)
      (((TopRep.homogeneousCochains T).iCycles (p + (q + r))
        (discreteContinuousCupCocycles A (discreteTensorCoefficient B C) p (q + r) x
          (discreteContinuousCupCocycles B C q r y z))).val) t =
      av ⊗ₜ[R] (bv ⊗ₜ[R] cv) :=
    hr₀.trans (congrArg (fun v : discreteTensorCoefficient B C => av ⊗ₜ[R] v) hr₁)
  exact hd.trans (hm.trans ((congrArg (discreteTensorCoefficientAssociator A B C).hom.hom hl).trans
    ((discreteTensorCoefficientAssociator_hom_tmul A B C av bv cv).trans hr.symm)))

private theorem nativePi_surjective
    (X : TopRep.{max v w, u, v} R G) (n : ℕ) : Function.Surjective (π X n) := by
  exact (ModuleCat.epi_iff_surjective
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (π X n))).mp inferInstance

/-- Let R be a commutative ring with a topology, G a profinite group,
and A,B,C topological R-representations with discrete coefficient topologies.
The tensor coefficients have their discrete diagonal G-actions.
For x ∈ Hᵖ_cts(G,A), y ∈ Hᑫ_cts(G,B), and z ∈ Hʳ_cts(G,C),
the coefficient associator and degree identification send
(x ∪ y) ∪ z to x ∪ (y ∪ z). -/
theorem discreteContinuousCup_assoc
    (A B C : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C]
    (p q r : ℕ) (x : continuousCohomology p A) (y : continuousCohomology q B)
    (z : continuousCohomology r C) :
    ((ContinuousCohomology.map
        (X := discreteTensorCoefficient (discreteTensorCoefficient A B) C)
        (Y := discreteTensorCoefficient A (discreteTensorCoefficient B C))
        (ContinuousMonoidHom.id G) (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r)) ≫
      eqToHom (congrArg (fun n => continuousCohomology n
        (discreteTensorCoefficient A (discreteTensorCoefficient B C))) (Nat.add_assoc p q r))).hom
      (discreteContinuousCup (discreteTensorCoefficient A B) C (p + q) r
        (discreteContinuousCup A B p q x y) z) =
      discreteContinuousCup A (discreteTensorCoefficient B C) p (q + r) x
        (discreteContinuousCup B C q r y z) := by
  obtain ⟨a, rfl⟩ := nativePi_surjective A p x
  obtain ⟨b, rfl⟩ := nativePi_surjective B q y
  obtain ⟨c, rfl⟩ := nativePi_surjective C r z
  let L := discreteTensorCoefficient (discreteTensorCoefficient A B) C
  let T := discreteTensorCoefficient A (discreteTensorCoefficient B C)
  let zl := discreteContinuousCupCocycles (discreteTensorCoefficient A B) C (p + q) r
    (discreteContinuousCupCocycles A B p q a b) c
  let H : continuousCohomology ((p + q) + r) L ⟶ continuousCohomology (p + (q + r)) T :=
    ContinuousCohomology.map (X := L) (Y := T) (ContinuousMonoidHom.id G)
      (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => continuousCohomology n T) (Nat.add_assoc p q r))
  have hl : discreteContinuousCup (discreteTensorCoefficient A B) C (p + q) r
      (discreteContinuousCup A B p q (π A p a) (π B q b)) (π C r c) = π L ((p + q) + r) zl :=
    (congrArg (fun v => discreteContinuousCup (discreteTensorCoefficient A B) C
        (p + q) r v (π C r c))
      (discreteContinuousCup_pi A B p q a b)).trans
        (discreteContinuousCup_pi (discreteTensorCoefficient A B) C (p + q) r
          (discreteContinuousCupCocycles A B p q a b) c)
  have hm₀ : H.hom (π L ((p + q) + r) zl) =
      (eqToHom (congrArg (fun n => continuousCohomology n T) (Nat.add_assoc p q r))).hom
        (ContinuousCohomology.map (X := L) (Y := T) (ContinuousMonoidHom.id G)
          (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r)
              (π L ((p + q) + r) zl)) := rfl
  have hm₁ := congrArg
    (eqToHom (congrArg (fun n => continuousCohomology n T) (Nat.add_assoc p q r))).hom
    (ConcreteCategory.congr_hom
      (π_map (X := L) (Y := T) (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r)) zl)
  have hm₂ := nativePi_degree_transport T ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    (cocyclesMap (X := L) (Y := T) (ContinuousMonoidHom.id G)
      (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r) zl)
  have hm₃ := congrArg (π T (p + (q + r))) (discreteContinuousCupCocycles_assoc A B C p q r a b c)
  have hr₀ := (discreteContinuousCup_pi A (discreteTensorCoefficient B C) p (q + r) a
    (discreteContinuousCupCocycles B C q r b c)).symm
  have hr₁ := congrArg (fun v => discreteContinuousCup A (discreteTensorCoefficient B C)
    p (q + r) (π A p a) v) (discreteContinuousCup_pi B C q r b c).symm
  exact (congrArg H.hom hl).trans
    (hm₀.trans (hm₁.trans (hm₂.trans (hm₃.trans (hr₀.trans hr₁)))))

end ContinuousCohomology
