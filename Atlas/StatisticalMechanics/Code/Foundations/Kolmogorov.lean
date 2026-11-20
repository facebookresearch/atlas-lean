/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























import Code.Foundations.ConfigSpace

open MeasureTheory

namespace StatMech

namespace Kolmogorov

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]






noncomputable def extension : Measure (Π i, X i) := Measure.infinitePi μ


instance isProbabilityMeasure : IsProbabilityMeasure (extension μ) := by
  unfold extension; infer_instance

theorem extension_isProbabilityMeasure : IsProbabilityMeasure (extension μ) :=
  isProbabilityMeasure μ







theorem extension_isProjectiveLimit :
    IsProjectiveLimit (extension μ) (fun I : Finset ι => Measure.pi (fun i : I => μ i)) :=
  Measure.isProjectiveLimit_infinitePi μ



theorem extension_map_restrict (I : Finset ι) :
    (extension μ).map I.restrict = Measure.pi (fun i : I => μ i) :=
  Measure.isProjectiveLimit_infinitePi μ I




theorem extension_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    extension μ (cylinder I S) = Measure.pi (fun i : I => μ i) S :=
  Measure.infinitePi_cylinder μ hS



theorem extension_pi {s : Finset ι} {t : (i : ι) → Set (X i)}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    extension μ (Set.pi s t) = ∏ i ∈ s, μ i (t i) :=
  Measure.infinitePi_pi μ ht






theorem extension_unique {ν : Measure (Π i, X i)}
    (hν : ∀ (s : Finset ι) (t : (i : ι) → Set (X i)),
      (∀ i, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
    ν = extension μ :=
  Measure.eq_infinitePi μ hν




theorem extension_unique_of_isProjectiveLimit {ν : Measure (Π i, X i)}
    (hν : IsProjectiveLimit ν (fun I : Finset ι => Measure.pi (fun i : I => μ i))) :
    ν = extension μ :=
  hν.unique (extension_isProjectiveLimit μ)

end Kolmogorov








namespace Kolmogorov

variable {E : Type*} (μ : E → Measure Bool) [∀ e, IsProbabilityMeasure (μ e)]



noncomputable def configExtension : Measure (ConfigSpace E) := extension μ


instance : IsProbabilityMeasure (configExtension μ) := by
  unfold configExtension; infer_instance



theorem configExtension_isProjectiveLimit :
    IsProjectiveLimit (configExtension μ)
      (fun I : Finset E => Measure.pi (fun e : I => μ e)) :=
  extension_isProjectiveLimit μ



theorem configExtension_unique {ν : Measure (ConfigSpace E)}
    (hν : ∀ (s : Finset E) (t : E → Set Bool),
      (∀ e, MeasurableSet (t e)) → ν (Set.pi s t) = ∏ e ∈ s, μ e (t e)) :
    ν = configExtension μ :=
  extension_unique μ hν

end Kolmogorov

end StatMech
