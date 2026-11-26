# The closure dimension characterizes uniform generatability

Let $U$ be countable and $H \subseteq \{0,1\}^U$ a class all of whose supports are infinite. Then $H$ is uniformly generatable if and only if $\mathrm{C}(H) < \infty$; in that case $\mathrm{C}(H) + 1$ distinct examples suffice. Moreover $H$ is non-uniformly generatable if and only if $H = \bigcup_{n} H_n$ for a nondecreasing sequence of classes with $\mathrm{C}(H_n) < \infty$ for every $n$, and every finite union of classes of finite closure dimension is generatable in the limit. Generatability and predictability are incomparable: there are classes that are uniformly generatable but not PAC or online learnable, and classes that are learnable but not generatable.

## Proof sketch

If $\mathrm{C}(H) = d$, after $d+1$ distinct examples the closure of the seen set is infinite (or the seen set is not realizable), so outputting an unseen element of the closure is valid for every consistent hypothesis, in particular the target. If $\mathrm{C}(H) = \infty$, the adversary presents $x_1, \dots, x_d$ with finite nonempty closure for arbitrarily large $d$; after the closure is exhausted, every output fails for some consistent hypothesis, defeating any fixed $d^*$. The non-uniform characterization runs the uniform generators of the $H_n$ in a dovetailed fashion.

## Depends on

- [Closure dimension and uniform and non-uniform generatability](closure-dimension.md)
- [Generation in the limit](generation-in-the-limit.md)

## Proof depends on

- [The fundamental theorem of PAC learning](../pac-learning/is-paclearnable-realizable-family-iff-ha.md)
- [The Littlestone dimension is the optimal mistake bound](../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Sources

- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
