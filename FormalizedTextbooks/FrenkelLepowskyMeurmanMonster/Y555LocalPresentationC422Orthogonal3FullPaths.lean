/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original acyclic source paths lift to isometries of the independent finite form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3TPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3FullGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each literal original source reflection is an actual independent form isometry. -/
def y422Orthogonal3FullGenerator (i : Fin 9) : y422Orthogonal3FullGroup :=
  ⟨y422Orthogonal3Generator i, y422Orthogonal3Reflection_preserves i⟩

/-- Every actual original acyclic path, evaluated in the independent full isometry group. -/
noncomputable def y422Orthogonal3FullTPath (i : Fin 9033) : y422Orthogonal3FullGroup :=
  y522WordProgramValue y422TPathProgram y422Orthogonal3FullGenerator i

/-- The independent isometry lift retains exactly the actual original linear source-word action. -/
theorem y422Orthogonal3FullTPath_value (i : Fin 9033) :
    (y422Orthogonal3FullTPath i).val = y422Orthogonal3TPathValue i := by
  change y422Orthogonal3FullGroup.subtype
    (y522WordProgramValue y422TPathProgram y422Orthogonal3FullGenerator i) = _
  rw [y522WordProgramValue_map]
  rfl

/-- Every original linear acyclic path is an actual independent finite-form isometry. -/
theorem y422Orthogonal3TPathValue_mem_full (i : Fin 9033) :
    y422Orthogonal3TPathValue i ∈ y422Orthogonal3FullGroup := by
  rw [← y422Orthogonal3FullTPath_value]
  exact (y422Orthogonal3FullTPath i).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
