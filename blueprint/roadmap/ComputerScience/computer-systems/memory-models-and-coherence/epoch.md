# Epoch

A snapshot for one location in an epoch, with an end value if it was a read–write epoch.
The logical start value, per-core readable values, and write permissions can be inconsistent;
coherence is checked by separate predicates.
