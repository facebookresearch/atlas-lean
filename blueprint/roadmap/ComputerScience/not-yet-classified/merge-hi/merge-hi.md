# Merge Hi?

Transcription of CPython's right-to-left stable merge.

`ssa` and `ssb` are signed base indices into `state.data`; `na` and `nb` are
their positive, signed-`Py_ssize_t`-representable lengths.  Adjacency is an
assertion-domain check.  No `na ≥ nb` check is added because the pinned C
routine documents that selection condition but does not assert it locally.
