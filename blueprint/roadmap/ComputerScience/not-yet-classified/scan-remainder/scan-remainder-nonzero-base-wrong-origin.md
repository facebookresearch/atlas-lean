# Scan Remainder nonzero base wrong origin rejected

Nonzero-base/origin regression.  A mistaken zero-based comparison would
match exactly, and the correctly selected range has the right visible values;
nevertheless the invariant rejects it because absolute origin two was changed
to one.  Thus neither the base offset nor origin equality can be erased
silently.
