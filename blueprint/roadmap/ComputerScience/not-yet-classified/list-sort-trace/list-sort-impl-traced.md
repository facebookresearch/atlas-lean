# List Sort Impl Traced?

Genuine traced snapshot-model `list_sort_impl`.  Initial reverse-sort
instrumentation uses `sortsliceReverseTraced?`: keyed execution records the key
phase followed by the synchronized-values phase, both from the same paired
snapshot.
