# Array Read?

Low-level array-read instrumenter shared by the region-specific wrappers.
Negative and past-the-end attempts return `none` only after their event has
been formed.  Callers should not supply ad-hoc labels for listsort storage.
