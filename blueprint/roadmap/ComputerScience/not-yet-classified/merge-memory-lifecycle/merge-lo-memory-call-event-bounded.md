# Merge Lo Memory Call Event bounded

A valid literal `merge_lo` record is bounded once the caller supplies the
bound threaded from `merge_init`.  The optional freed snapshot is checked
against the actual `mergeFreemem` transition rather than discarded.
