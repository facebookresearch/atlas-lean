# Push Pending Run

The source pending-run write, modeled as an unconditional operation on an
unbounded Lean array.  In particular, a 64-entry input becomes 65 entries;
the later policy theorem proves that valid top-level executions never reach
that artificial input.
