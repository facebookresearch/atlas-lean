# Deviatoric stress

For a real `3 × 3` matrix `σ`, the deviatoric stress is `s = σ - σₘ 1`, where `σₘ = tr σ / 3` is the
[mean stress](mean-stress.md) and `1` is the identity matrix. It is
[traceless](trace-deviatoric.md), and `σ = σₘ 1 + s` is the [unique](stress-split-unique.md) split
of `σ` into a multiple of the identity and a traceless matrix.
