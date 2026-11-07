# Permutations with only even cycles fix no self-dual monotone function (Lemma 15)

Let
$\pi$ be a permutation of $\{0, \dots, n-1\}$ all of whose cycles have even length, that is,
every point has an orbit of even size under $\pi$. Let $f : \{0,1\}^n \to \{0,1\}$ be self-dual
monotone, that is, monotone for the coordinatewise order with $0 < 1$ and such that
$f(\bar x) = \lnot f(x)$ for every $x$, where $\bar x$ is the coordinatewise complement of $x$.
Then $f$ is not fixed by $\pi$: the function $x \mapsto f(x \circ \pi)$, where
$(x \circ \pi)_i = x_{\pi(i)}$, differs from $f$.

The paper also assumes that $n$ is even; this follows from the condition on the cycles.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 15 (`jis-2025-25.6.5-lem-15`).
