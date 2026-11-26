# Definition of the mixing time of the interchange process on the hypercube

Let $n \in \mathbb{N}$ and let $d(t)$ be the [distance to uniformity](interchange-dist-to-uniform.md) at time $t$ of the unit-rate interchange process on the hypercube $\{0,1\}^n$ started at the identity: for $t \ge 0$, the total variation distance between the law of the process at time $t$ and the uniform distribution on permutations of $\{0, 1\}^n$. The mixing time is

$$t_{\mathrm{mix}}(n) = \inf\{t \ge 0 : d(t) \le e^{-1}\},$$

the threshold $1/e$ being the convention of Hermon and Salez. The infimum of the empty set is read as $0$.
