# Found New Run?

Transcription of CPython's `found_new_run`.

The empty-stack branch is an explicit no-op.  For a nonempty stack, the guard
records the assertion domain inherited from `powerloop`: adjacent run lengths
are positive and the two runs lie within the nonnegative list length.  A
failure of the fixed 64-step power loop is observable as fuel exhaustion.
The source's debug-only post-loop strictness assertion is not turned into a
release-mode refusal branch.
