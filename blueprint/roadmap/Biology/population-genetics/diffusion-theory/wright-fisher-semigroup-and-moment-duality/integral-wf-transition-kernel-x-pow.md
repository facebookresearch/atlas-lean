# Kernel form of Wright–Fisher moment duality

For every real $t \ge 0$, every natural number $n$ and every $x \in [0, 1]$, the $n$-th moment of the [Wright–Fisher transition kernel](wf-transition-kernel.md) is

$$\int y^n\, K_t(x, dy) = \sum_{k=0}^{n} \bigl(e^{t G_n}\bigr)(n, k)\, x^k,$$

the generating polynomial, evaluated at $x$, of the transition probabilities from $n$ lineages of [Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md).
