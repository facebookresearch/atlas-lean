# Entry Snapshot Permutation

The current slice contains exactly the absolutely tagged source entries,
including their optional payloads.  This invariant deliberately ranges over
the whole array, so local correctness posts can preserve it by a frame plus a
whole-entry permutation of the modified range.
