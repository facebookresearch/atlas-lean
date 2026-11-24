# Merge Lo pending eq of eq some

`merge_lo` mutates data, temporary storage, allocation metadata, and the
adaptive gallop threshold, but never the pending-run stack.
