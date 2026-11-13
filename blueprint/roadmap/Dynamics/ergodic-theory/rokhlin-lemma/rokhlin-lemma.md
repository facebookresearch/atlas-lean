# Rokhlin lemma for non-invertible maps

Let $\Omega$ be a standard Borel space with a
probability measure $\mu$, and let $T : \Omega \to \Omega$ be a measure-preserving map that is
aperiodic with respect to $\mu$. Then for every integer $n \ge 1$ and every
$\varepsilon \in (0, \infty]$ there is a measurable set $B \subseteq \Omega$ such that the
floors $B, T(B), \dots, T^{n-1}(B)$ are pairwise disjoint, where $T^k(B)$ is the image of $B$
under the $k$-fold iterate of $T$, and their union $\bigcup_{k=0}^{n-1} T^k(B)$ has outer
$\mu$-measure at least $1 - \varepsilon$ (truncated subtraction, so the bound is $0$ when
$\varepsilon \ge 1$). No invertibility of $T$ is assumed.

## Sources

- V. A. Rokhlin, *A general measure-preserving transformation is not mixing*, Doklady Akademii Nauk SSSR 60 (1948), 349-351 (original Russian; English translation later); S. Kakutani, *Induced measure-preserving transformations*, Proc. Imp. Acad. Tokyo 19 (1943), 635-641 (independent discovery); S.-M. Heinemann and O. Schmitt, *Rokhlin's lemma for non-invertible maps*, Dynam. Systems Appl. 10 (2001), no. 2, 201-213. The classical form is listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `rokhlin_lemma` of the lean-eval benchmark.
