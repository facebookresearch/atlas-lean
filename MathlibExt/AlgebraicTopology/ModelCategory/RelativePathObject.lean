/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Actual relative path objects from the given model factorization

Factor the original diagonal into the pullback of a map with itself.
Both complete endpoint maps have the same image in the given base.
For a fibration, the endpoint projections are trivial fibrations.
The original factorization also gives a compatible whole map to any
given good absolute path object, with the diagonal retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.RelativePathObject

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (data : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  {X S : C} (p : X ⟶ S)

/-- The same original object enters the actual relative endpoint pullback. -/
def diagonal : X ⟶ pullback p p := pullback.lift (𝟙 X) (𝟙 X) rfl

/-- Use the given native factorization on this actual relative diagonal. -/
abbrev factor : MapFactorizationData (trivialCofibrations C) (fibrations C) (diagonal p) :=
  data.factorizationData (diagonal p)

/-- Both whole endpoints and the original factorization unit define the relative prepath. -/
def prepath : PrepathObject X where
  P := (factor data p).Z
  p₀ := (factor data p).p ≫ pullback.fst p p
  p₁ := (factor data p).p ≫ pullback.snd p p
  ι := (factor data p).i
  ι_p₀ := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ pullback.fst p p) (factor data p).fac).trans
      (pullback.lift_fst _ _ _))
  ι_p₁ := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ pullback.snd p p) (factor data p).fac).trans
      (pullback.lift_snd _ _ _))

/-- The same original factorization unit is weak, giving the actual relative path object. -/
def pathObject : PathObject X where
  __ := prepath data p
  weakEquivalence_ι := (weakEquivalence_iff _).mpr (factor data p).hi.2

/-- The entire original relative endpoint map is the given second factor. -/
def relativeEndpoints : (pathObject data p).P ⟶ pullback p p := (factor data p).p

/-- Its actual relative endpoint map is a fibration by the supplied native factorization. -/
theorem relativeEndpoints_fibration : fibrations C (relativeEndpoints data p) :=
  (factor data p).hp

/-- Both complete original endpoint maps retain exactly the same base projection. -/
theorem fixed_base : (pathObject data p).p₀ ≫ p = (pathObject data p).p₁ ≫ p :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m => (factor data p).p ≫ m) (pullback.condition (f := p) (g := p))).trans
      (Category.assoc _ _ _).symm)

/-- The same original unit is a trivial cofibration. -/
theorem unit_trivialCofibration : trivialCofibrations C (pathObject data p).ι :=
  (factor data p).hi

/-- A genuine base fibration gives a fibration of the actual first projection. -/
theorem first_fibration [Fibration p] : Fibration (pathObject data p).p₀ := by
  let _ : Fibration (factor data p).p := (fibration_iff _).mpr (factor data p).hp
  change Fibration ((factor data p).p ≫ pullback.fst p p)
  infer_instance

/-- The actual opposite projection is also fibrational over a genuine base fibration. -/
theorem second_fibration [Fibration p] : Fibration (pathObject data p).p₁ := by
  let _ : Fibration (factor data p).p := (fibration_iff _).mpr (factor data p).hp
  change Fibration ((factor data p).p ≫ pullback.snd p p)
  infer_instance

/-- The first endpoint is weak by the same unit retraction and hence genuinely trivial fibrational.
-/
theorem first_trivialFibration [Fibration p] : trivialFibrations C (pathObject data p).p₀ :=
  ⟨(fibration_iff _).mp (first_fibration data p), (weakEquivalence_iff _).mp inferInstance⟩

/-- The same unit also makes the opposite original endpoint trivial fibrational. -/
theorem second_trivialFibration [Fibration p] : trivialFibrations C (pathObject data p).p₁ :=
  ⟨(fibration_iff _).mp (second_fibration data p), (weakEquivalence_iff _).mp inferInstance⟩

/-- The actual relative path diagram is fibrant over a fibrant original source. -/
theorem fibrant [Fibration p] [IsFibrant X] : IsFibrant (pathObject data p).P := by
  let _ := first_fibration data p
  exact isFibrant_of_fibration (pathObject data p).p₀

variable (Q : PathObject X) [Q.IsGood]

omit [Q.IsGood] in
private theorem comparisonSquare : CommSq Q.ι (pathObject data p).ι Q.p (pathObject data p).p := by
  constructor
  apply prod.hom_ext <;>
    simp only [Category.assoc, PrepathObject.p_fst, PrepathObject.p_snd,
      PrepathObject.ι_p₀, PrepathObject.ι_p₁]

/-- The genuine original lifting axiom gives a whole map into the prescribed good path, retaining
its diagonal. -/
def toGood : (pathObject data p).P ⟶ Q.P := by
  let _ : Cofibration (pathObject data p).ι := (cofibration_iff _).mpr (unit_trivialCofibration data
    p).1
  let _ : HasLiftingProperty (pathObject data p).ι Q.p := ModelCategory.cm4a _ _
  exact (comparisonSquare data p Q).lift

/-- The entire given original diagonal is the same after this actual relative comparison. -/
theorem toGood_diagonal : (pathObject data p).ι ≫ toGood data p Q = Q.ι := by
  let _ : Cofibration (pathObject data p).ι := (cofibration_iff _).mpr (unit_trivialCofibration data
    p).1
  let _ : HasLiftingProperty (pathObject data p).ι Q.p := ModelCategory.cm4a _ _
  exact (comparisonSquare data p Q).fac_left

/-- Both whole absolute endpoint maps are retained by the same comparison. -/
theorem toGood_pair : toGood data p Q ≫ Q.p = (pathObject data p).p := by
  let _ : Cofibration (pathObject data p).ι := (cofibration_iff _).mpr (unit_trivialCofibration data
    p).1
  let _ : HasLiftingProperty (pathObject data p).ι Q.p := ModelCategory.cm4a _ _
  exact (comparisonSquare data p Q).fac_right

/-- The whole first original projection is unchanged under comparison with the prescribed good path.
-/
theorem toGood_first : toGood data p Q ≫ Q.p₀ = (pathObject data p).p₀ :=
  (congrArg (fun m => toGood data p Q ≫ m) Q.p_fst.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ prod.fst) (toGood_pair data p Q)).trans
        (pathObject data p).p_fst))

/-- Its opposite whole original projection is also unchanged. -/
theorem toGood_second : toGood data p Q ≫ Q.p₁ = (pathObject data p).p₁ :=
  (congrArg (fun m => toGood data p Q ≫ m) Q.p_snd.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ prod.snd) (toGood_pair data p Q)).trans
        (pathObject data p).p_snd))

variable {T : C} {f g : T ⟶ X}

/-- Every supplied whole relative right homotopy is transported to the same prescribed good path. -/
def postHomotopy (H : (pathObject data p).RightHomotopy f g) : Q.RightHomotopy f g where
  h := H.h ≫ toGood data p Q
  h₀ := (Category.assoc _ _ _).trans
    ((congrArg (fun m => H.h ≫ m) (toGood_first data p Q)).trans H.h₀)
  h₁ := (Category.assoc _ _ _).trans
    ((congrArg (fun m => H.h ≫ m) (toGood_second data p Q)).trans H.h₁)

/-- The full original parameter map is retained in the transported right homotopy. -/
theorem postHomotopy_map (H : (pathObject data p).RightHomotopy f g) :
    (postHomotopy data p Q H).h = H.h ≫ toGood data p Q := rfl

/-- A relative right homotopy gives equality of the two complete original base maps. -/
theorem homotopy_fixed_base (H : (pathObject data p).RightHomotopy f g) : f ≫ p = g ≫ p :=
  (congrArg (fun m => m ≫ p) H.h₀.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => H.h ≫ m) (fixed_base data p)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ p) H.h₁))))

end HomotopicalAlgebra.RelativePathObject
