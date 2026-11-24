# List Sort Impl?

Snapshot-model transcription of CPython's `list_sort_impl`.

The input-size guard is the selected platform's list-allocation bound.  A
pending run is always installed with `Array.push`; this definition contains no
`MAX_MERGE_PENDING` test and no modeled debug-assertion failure.  `none`
denotes an invalid modeled access or assertion-domain input, while bounded-loop
exhaustion is returned explicitly.
