# Lazy = eager

**Lazy = eager** (generic form). Suppose that, for every table `T` satisfying an invariant
`Inv` and every fresh query `x`, the uniform distribution on the functions consistent with `T`
splits as "sample the answer from `fresh T x`, then sample uniformly among the functions
consistent with `T` extended by `x ↦ y`", and that fresh steps preserve `Inv`. Then for every
adaptive algorithm `c`, the lazy run has the output distribution of `c` run against a function
sampled uniformly among those consistent with `T`.
