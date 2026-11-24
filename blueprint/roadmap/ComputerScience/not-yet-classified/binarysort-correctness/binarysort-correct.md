# Binarysort correct

The source-admitted traced evaluator safely returns the stable sorted
permutation of its target range.  No law beyond `BoolStrictWeakOrder` is added
to the modeled comparator, and the proof identifies the functional result via
the safety theorem's exact erasure field.
