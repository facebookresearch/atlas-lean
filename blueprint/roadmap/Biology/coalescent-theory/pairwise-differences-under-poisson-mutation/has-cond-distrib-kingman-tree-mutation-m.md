# Conditional law of the counts given the genealogy in the marked model

For every natural number `n` and every `θ ≥ 0`, under the
[marked Kingman model](kingman-tree-mutation-measure.md) the vector `N` of mutation counts has
conditional law the [mutation kernel with topology](kingman-tree-mutation-kernel.md) given the
genealogy `((T_2, …, T_n), h)`, where the `T_k` are the
[holding times of the marked model](of-tree-mutation-model.md) and `h` is the history
coordinate: the pair formed by the genealogy and `N` is almost everywhere measurable, and its law
is the composition of the law of the genealogy with the kernel. Given the genealogy, the counts
`N_b` are independent, `N_b` Poisson with mean `θ / 2` times the length of branch `b`.
