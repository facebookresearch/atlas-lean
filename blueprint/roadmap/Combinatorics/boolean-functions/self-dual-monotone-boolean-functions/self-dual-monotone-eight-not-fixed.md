# Permutations of eight variables fixing no self-dual monotone function (Corollary 16)

Let $\pi$ be one of the permutations $(0\,1\,2\,3\,4\,5\,6\,7)$, $(0\,1)(2\,3\,4\,5\,6\,7)$,
$(0\,1\,2\,3)(4\,5\,6\,7)$, $(0\,1)(2\,3)(4\,5\,6\,7)$ and $(0\,1)(2\,3)(4\,5)(6\,7)$ of
$\{0, \dots, 7\}$, in cycle notation. Let $f : \{0,1\}^8 \to \{0,1\}$ be self-dual monotone,
that is, monotone for the coordinatewise order with $0 < 1$ and such that
$f(\bar x) = \lnot f(x)$ for every $x$, where $\bar x$ is the coordinatewise complement of $x$.
Then $f$ is not fixed by $\pi$: the function $x \mapsto f(x \circ \pi)$, where
$(x \circ \pi)_i = x_{\pi(i)}$, differs from $f$.

In the paper the points are numbered $1, \dots, 8$, so these permutations are $(12345678)$,
$(12)(345678)$, $(1234)(5678)$, $(12)(34)(5678)$ and $(12)(34)(56)(78)$.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 16 (`jis-2025-25.6.5-cor-16`).
