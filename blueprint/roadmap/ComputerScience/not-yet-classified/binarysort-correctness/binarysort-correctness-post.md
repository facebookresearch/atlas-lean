# Binarysort Correctness Post

Public correctness certificate for the exact traced `binarysort`
execution.  The stability premise is intentionally attached to the whole
target range: binary insertion preserves the pre-existing order of equal
occurrences, so it cannot repair an already non-canonical equal-key suffix.
