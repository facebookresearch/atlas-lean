/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# Compatible fixed-cardinal base generation witnesses

This opt-in predicate records existence of actual base generation data at
one regular cardinal. It is independent of local presentability. It does
not replace the conventional theorem converting uniform relative source
smallness to fixed-cardinal eligibility.

Selection chooses only the existing base witness. The source model,
generating maps, ordinal bottom, and actual factors remain visible; no
instance of generation data or of a diagram model is installed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

/-- Existence of actual compatible base generation data in the working universe. -/
@[pp_with_univ]
class HasCompatibleCofibrantGeneration (M : Type u) [Category.{v} M] [ModelCategory M] : Prop where
  exists_data : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
    Nonempty (CofibrantGenerationData M κ)

namespace HasCompatibleCofibrantGeneration
variable {M : Type u} [Category.{v} M] [ModelCategory M]

/-- Any supplied complete fixed-cardinal datum gives compatible generation existence. -/
theorem ofData {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) : HasCompatibleCofibrantGeneration.{w} M :=
  ⟨κ, inferInstance, inferInstance, ⟨d⟩⟩

/-- A combinatorial base supplies this weaker predicate by forgetting presentability. -/
theorem ofCombinatorial [IsCombinatorialModelCategory.{w} M] :
    HasCompatibleCofibrantGeneration.{w} M := by
  obtain ⟨κ, hκ, hb, _, hd⟩ := IsCombinatorialModelCategory.exists_cardinal (C := M)
  exact ⟨κ, hκ, hb, hd⟩

variable [h : HasCompatibleCofibrantGeneration.{w} M]

/-- The selected cardinal belongs to the actual existing base-generation witness. -/
def cardinal : Cardinal.{w} := h.exists_data.choose

/-- The selected cardinal retains its actual regularity witness. -/
theorem cardinal_regular : Fact (cardinal (M := M)).IsRegular :=
  h.exists_data.choose_spec.choose

/-- The selected ordinal bottom belongs to that same existing base witness. -/
@[instance_reducible]
def orderBot : OrderBot (cardinal (M := M)).ord.ToType :=
  h.exists_data.choose_spec.choose_spec.choose

/-- The same selected cardinal and bottom have actual nonempty base generation data. -/
theorem data_nonempty :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    Nonempty (CofibrantGenerationData M (cardinal (M := M))) :=
  h.exists_data.choose_spec.choose_spec.choose_spec

/-- Choose the actual base datum at that same cardinal and supplied ordinal bottom. -/
def data :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    CofibrantGenerationData M (cardinal (M := M)) :=
  Classical.choice data_nonempty

/-- The selected I family is the actual stored base generating family. -/
def generatingCofibrations : MorphismProperty M := by
  letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).I

/-- The selected J family is the actual stored base trivial-generating family. -/
def generatingTrivialCofibrations : MorphismProperty M := by
  letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).J

/-- The complete selected I family is eligible at the original selected cardinal. -/
theorem generatingCofibrations_eligible :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    (generatingCofibrations (M := M)).IsCardinalForSmallObjectArgument (cardinal (M := M)) := by
  let _ : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).I_smallObject

/-- The complete selected J family is eligible at that same cardinal. -/
theorem generatingTrivialCofibrations_eligible :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    (generatingTrivialCofibrations (M := M)).IsCardinalForSmallObjectArgument
      (cardinal (M := M)) := by
  let _ : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).J_smallObject

/-- The selected I right class is the original base trivial-fibration class. -/
theorem generatingCofibrations_rlp :
    (generatingCofibrations (M := M)).rlp = trivialFibrations M := by
  let _ : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).I_rlp

/-- The selected J right class is the original base fibration class. -/
theorem generatingTrivialCofibrations_rlp :
    (generatingTrivialCofibrations (M := M)).rlp = fibrations M := by
  let _ : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  let _ : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).J_rlp

/-- The selected I factor data is the already proved getter for the same selected datum. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData (cofibrations M) (trivialFibrations M) := by
  letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).cofibrantFactorizationData

/-- The selected J factor data is the same-datum getter at the same cardinal. -/
def fibrantFactorizationData :
    FunctorialFactorizationData (trivialCofibrations M) (fibrations M) := by
  letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact (data (M := M)).fibrantFactorizationData

/-- The actual selected I maps factor every original base arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow M) :
    (cofibrantFactorizationData (M := M)).i.app f ≫
      (cofibrantFactorizationData (M := M)).p.app f = f.hom :=
  (cofibrantFactorizationData (M := M)).fac_app

/-- The actual selected J maps factor every original base arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow M) :
    (fibrantFactorizationData (M := M)).i.app f ≫
      (fibrantFactorizationData (M := M)).p.app f = f.hom :=
  (fibrantFactorizationData (M := M)).fac_app

/-- The whole selected cofibrant middle functor is the original selected-family SOA. -/
theorem cofibrantFactorizationData_Z :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    letI : (generatingCofibrations (M := M)).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
      generatingCofibrations_eligible
    (cofibrantFactorizationData (M := M)).Z =
      (SmallObject.functorialFactorizationData (generatingCofibrations (M :=
      M)) (cardinal (M := M))).Z := rfl

/-- Every original Arrow square retains naturality of the selected cofibrant left map. -/
theorem cofibrantFactorizationData_i_naturality {f g : Arrow M} (φ : f ⟶ g) :
    φ.left ≫ (cofibrantFactorizationData (M := M)).i.app g =
      (cofibrantFactorizationData (M :=
      M)).i.app f ≫ (cofibrantFactorizationData (M := M)).Z.map φ :=
  (cofibrantFactorizationData (M := M)).i.naturality φ

/-- Every original Arrow square retains naturality of the selected cofibrant right map. -/
theorem cofibrantFactorizationData_p_naturality {f g : Arrow M} (φ : f ⟶ g) :
    (cofibrantFactorizationData (M := M)).Z.map φ ≫ (cofibrantFactorizationData (M := M)).p.app g =
      (cofibrantFactorizationData (M := M)).p.app f ≫ φ.right :=
  (cofibrantFactorizationData (M := M)).p.naturality φ

/-- The actual selected cofibrant middle functor preserves original Arrow identities. -/
theorem cofibrantFactorizationData_map_id (f : Arrow M) :
    (cofibrantFactorizationData (M :=
      M)).Z.map (𝟙 f) = 𝟙 ((cofibrantFactorizationData (M := M)).Z.obj f) :=
  (cofibrantFactorizationData (M := M)).Z.map_id f

/-- The actual selected cofibrant middle functor preserves original Arrow composition. -/
theorem cofibrantFactorizationData_map_comp {f g k : Arrow M} (φ : f ⟶ g) (ψ : g ⟶ k) :
    (cofibrantFactorizationData (M := M)).Z.map (φ ≫ ψ) =
      (cofibrantFactorizationData (M :=
      M)).Z.map φ ≫ (cofibrantFactorizationData (M := M)).Z.map ψ :=
  (cofibrantFactorizationData (M := M)).Z.map_comp φ ψ

/-- The whole selected fibrant middle functor is the original selected-family SOA. -/
theorem fibrantFactorizationData_Z :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    letI : (generatingTrivialCofibrations (M :=
      M)).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
      generatingTrivialCofibrations_eligible
    (fibrantFactorizationData (M := M)).Z =
      (SmallObject.functorialFactorizationData (generatingTrivialCofibrations (M :=
      M)) (cardinal (M := M))).Z := rfl

/-- Every original Arrow square retains naturality of the selected fibrant left map. -/
theorem fibrantFactorizationData_i_naturality {f g : Arrow M} (φ : f ⟶ g) :
    φ.left ≫ (fibrantFactorizationData (M := M)).i.app g =
      (fibrantFactorizationData (M := M)).i.app f ≫ (fibrantFactorizationData (M := M)).Z.map φ :=
  (fibrantFactorizationData (M := M)).i.naturality φ

/-- Every original Arrow square retains naturality of the selected fibrant right map. -/
theorem fibrantFactorizationData_p_naturality {f g : Arrow M} (φ : f ⟶ g) :
    (fibrantFactorizationData (M := M)).Z.map φ ≫ (fibrantFactorizationData (M := M)).p.app g =
      (fibrantFactorizationData (M := M)).p.app f ≫ φ.right :=
  (fibrantFactorizationData (M := M)).p.naturality φ

/-- The actual selected fibrant middle functor preserves original Arrow identities. -/
theorem fibrantFactorizationData_map_id (f : Arrow M) :
    (fibrantFactorizationData (M :=
      M)).Z.map (𝟙 f) = 𝟙 ((fibrantFactorizationData (M := M)).Z.obj f) :=
  (fibrantFactorizationData (M := M)).Z.map_id f

/-- The actual selected fibrant middle functor preserves original Arrow composition. -/
theorem fibrantFactorizationData_map_comp {f g k : Arrow M} (φ : f ⟶ g) (ψ : g ⟶ k) :
    (fibrantFactorizationData (M := M)).Z.map (φ ≫ ψ) =
      (fibrantFactorizationData (M := M)).Z.map φ ≫ (fibrantFactorizationData (M := M)).Z.map ψ :=
  (fibrantFactorizationData (M := M)).Z.map_comp φ ψ

end HasCompatibleCofibrantGeneration
end HomotopicalAlgebra
