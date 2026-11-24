# Pointwise bound on the phenotype along a block design

For a [block design](block-design.md) with $N$ individuals, $M$ markers, block size $K$ and genotype
matrix $X$, $h^2 \in [0, 1]$, $\lambda \geq 0$ with $N \leq \lambda M$, a real number $C$ and
$\omega \in \mathbb{R}^{\mathbb{N}}$ with $|\omega_s| \leq C$ for every $s$, the phenotype
$y_i(\omega) = \sum_k X_{ik} \sqrt{h^2 / M}\, \omega_{2k} + \sqrt{1 - h^2}\, \omega_{2i+1}$ of the
[model on the product space](model-2.md) satisfies $y_i(\omega)^2 \leq 2 C^2 (K^2 \lambda + 1)$ for
every individual $i$.
