# Merge Getmem

Transcription of `merge_getmem` under the version-one convention that a
guard-admitted `PyMem_Malloc` call succeeds. The reuse test is signed, as in C.
The allocation guard views `need` through the same-width unsigned `size_t`
cast, represented by `need.toNat`. Fresh heap cells are uninitialized and old
payload contents are deliberately discarded rather than copied.
