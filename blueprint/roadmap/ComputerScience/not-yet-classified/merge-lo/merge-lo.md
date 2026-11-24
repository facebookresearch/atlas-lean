# Merge Lo?

Transcription of CPython's stable left-to-right merge.

`ssa` and `ssb` are signed pointer-like indices into `state.data`.  The public
guard mirrors the C assertion domain: both runs are positive and representable,
and the right run begins immediately after the left run.  The caller-side
choice `na ≤ nb` and endpoint ordering are intentionally not rechecked here,
matching their status as `merge_at` obligations in the C source.
