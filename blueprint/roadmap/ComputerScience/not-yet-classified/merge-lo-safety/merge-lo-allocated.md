# Merge Lo Allocated

The allocation selected by the concrete `merge_lo` call site.  Naming it
once keeps the preparation, core-execution, and final trace-witness stages in
lockstep without repeating the `merge_getmem` expression.
