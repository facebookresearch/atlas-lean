# Brent level bound

The arithmetic step of Brent's level-by-level bound: for any list `levels` of per-level task counts and `p ≥ 1`, running each level in `⌈w / p⌉` steps takes in total `∑ w ∈ levels, ⌈w / p⌉ ≤ (∑ w ∈ levels, w) / p + levels.length` steps. This is the natural-number form: `⌈w / p⌉` is written `(w + p - 1) / p` and `/` is truncating division.
