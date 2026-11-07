# Nearby expansions share long prefixes

Let $L$ be a list of natural numbers of length at
least $2$ with nonzero first entry, let $E^*$ be its $L^*$-collection, and let $Q$ be a strictly
decreasing sequence in $(0, 1)$ such that $\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a
bijection from $E^*$ onto $(0, 1)$; indices start at $0$. Let $\varepsilon \in E^*$, put
$x = \sum_k \varepsilon_k Q_k$, and let $n \in \mathbb N$. Define $\inf(\varepsilon)$ as follows:
if $\varepsilon$ has infinitely many nonzero entries, then $\inf(\varepsilon) = \varepsilon$;
otherwise, with $c$ the largest index such that $\varepsilon_c \ne 0$, $\inf(\varepsilon)$ agrees
with $\varepsilon$ at indices below $c$, has entry $\varepsilon_c - 1$ at index $c$, and agrees
at indices above $c$ with the maximal $L^*$-block starting at index $c + 1$. Then there is
$\delta > 0$ such that every $\varepsilon' \in E^*$ with
$x < \sum_k \varepsilon'_k Q_k < x + \delta$ satisfies $\varepsilon'_i = \varepsilon_i$ for all
$i \le n$, and every $\varepsilon' \in E^*$ with $x - \delta < \sum_k \varepsilon'_k Q_k < x$
satisfies $\varepsilon'_i = \inf(\varepsilon)_i$ for all $i \le n$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 5 (`integers-2025-A25-lem-5`; arXiv:2308.12872v1, Section 2.3).
