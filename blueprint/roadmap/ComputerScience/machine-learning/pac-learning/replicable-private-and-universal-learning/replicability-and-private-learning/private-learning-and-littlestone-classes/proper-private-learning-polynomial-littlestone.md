# Proper private learning of Littlestone classes with polynomial sample complexity

Let the domain $X$ and the class $F \subseteq \{-1, 1\}^X$ be countable, the paper's standing measurability assumption (Section 2.1). Every such class $F$ of Littlestone dimension $d$ is properly PAC learnable under $(\varepsilon, \delta)$-differential privacy from $n = \tilde O\big(d^6/(\varepsilon\alpha^2)\big)$ samples (with logarithmic factors in $1/\delta$ and the confidence suppressed), outputting with high probability a hypothesis of the class with error at most $\alpha$ on every realizable distribution; a generic reduction gives essentially the same bound in the agnostic setting. Moreover, for countable $X$ and $F$, the sample complexity of privately sanitizing (releasing accurate answers to all counting queries in) the binary class $F$ is polynomial in its Littlestone dimension and dual Littlestone dimension, so such a class is privately sanitizable if and only if it has finite Littlestone dimension.

## Proof sketch

A class $G$ is **irreducible** if for every point $x$ some label $b$ keeps the Littlestone dimension, $\mathrm{Ldim}(G|_{(x,b)}) = \mathrm{Ldim}(G)$ (and $k$-irreducible if the same holds along every depth-$k$ tree). Restricting the class by labelled examples that lower the Littlestone dimension reaches, after at most $d$ steps, an irreducible subclass, whose SOA classifier is determined by the class; the learner produces such candidates from many subsamples, releases the frequent ones with a private stable histogram, and selects a good one with the exponential mechanism on fresh samples, so its output lies in the class. Sanitization follows from private learning of the dual class.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Finite Littlestone dimension implies private learnability](littlestone-classes-are-privately-learnable.md)
- [The exponential mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)

## Sources

- B. Ghazi, N. Golowich, R. Kumar, P. Manurangsi, "Sample-efficient Proper PAC Learning with Approximate Differential Privacy", STOC (2021), arXiv:2012.03893, Theorem 1.1 (Theorem 6.4), Corollaries 1.2 and 1.3, Definition 4.1, Section 2.1.
