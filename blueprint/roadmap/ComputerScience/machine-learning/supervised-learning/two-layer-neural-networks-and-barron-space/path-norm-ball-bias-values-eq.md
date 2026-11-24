# Bias as an extra input coordinate

For a sample $x_1, \dots, x_n \in \mathbb{R}^d$ and $Q \in \mathbb{R}$, the
[path-norm ball with bias](path-norm-ball-bias-values.md) on the sample equals the
[path-norm ball without bias](path-norm-ball-values.md) on the sample
$(x_1, 1), \dots, (x_n, 1) \in \mathbb{R}^{d+1}$: appending the constant coordinate $1$ to every
sample point turns networks with bias into networks without bias in one more dimension.
