# $\varepsilon$ and $\inf(\varepsilon)$ have the same value

Let $L$ be a list of natural
numbers of length at least $2$ with nonzero first entry, let $E^*$ be the set of nonzero
coefficient functions $\mathbb N \to \mathbb N$ that are sums of finitely or infinitely many
disjoint proper $L^*$-blocks, and let $Q$ be a strictly decreasing sequence in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a bijection from $E^*$ onto $(0, 1)$; indices
start at $0$. For $\varepsilon \in E^*$ define $\inf(\varepsilon)$ as follows: if $\varepsilon$
has infinitely many nonzero entries, then $\inf(\varepsilon) = \varepsilon$; otherwise, with $c$
the largest index such that $\varepsilon_c \ne 0$, $\inf(\varepsilon)$ agrees with $\varepsilon$
at the indices below $c$, has entry $\varepsilon_c - 1$ at index $c$, and agrees at the indices
above $c$ with the maximal $L^*$-block starting at index $c + 1$. Then every
$\varepsilon \in E^*$ satisfies $\sum_k \varepsilon_k Q_k = \sum_k \inf(\varepsilon)_k Q_k$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 4 (`integers-2025-A25-lem-4`; arXiv:2308.12872v1, Section 2.3).
