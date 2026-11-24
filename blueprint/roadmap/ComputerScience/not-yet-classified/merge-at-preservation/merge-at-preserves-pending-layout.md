# Merge At preserves pending Layout

Every source-admitted `merge_at` result replaces exactly the selected
adjacent pair by its nonempty, signed-representable union, preserves every
unselected pending run, and preserves the layout of the same scanned prefix.

The theorem assumes no transitivity, consistency, or other comparator law.
