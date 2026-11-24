# Stable for forced range

If `count_run` finds a prefix shorter than the forced minrun target, its
stable output prefix followed by the untouched source suffix is already a
stable permutation of the entire target range.  This is the exact stability
premise consumed by `binarysort_correct`; it works for every admitted forced
length, not only for a particular minrun formula.
