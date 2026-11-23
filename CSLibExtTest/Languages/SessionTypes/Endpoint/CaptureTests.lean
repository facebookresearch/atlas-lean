/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Renaming
import CSLibExt.Languages.SessionTypes.Endpoint.ScopeTransport

/-!
# Nested input/restriction capture probes against existing π substitution
-/

namespace Cslib.SessionTypes.Endpoint.CaptureTests

open PiCalculus

/-- The received endpoint passes under a fresh ν without becoming its name. -/
theorem delegated_under_nu :
    subst (.nu (.out (.var 1) (.var 0) .nil)) (.var 0) =
      .nu (.out (.var 1) (.var 0) .nil) := rfl

/-- Replacement is shifted through BOTH an input and an inner restriction;
lifting only at the current cutoff would capture the outer channel. -/
theorem delegated_under_input_nu :
    subst (.inp (.var 0) (.nu (.out (.var 2) (.var 0) .nil))) (.var 0) =
      .inp (.var 0) (.nu (.out (.var 2) (.var 0) .nil)) := rfl

/-- The wrongly captured subject is a different existing π term. -/
theorem captured_subject_rejected :
    subst (.inp (.var 0) (.nu (.out (.var 2) (.var 0) .nil))) (.var 0) ≠
      .inp (.var 0) (.nu (.out (.var 1) (.var 0) .nil)) := by
  decide

end Cslib.SessionTypes.Endpoint.CaptureTests
