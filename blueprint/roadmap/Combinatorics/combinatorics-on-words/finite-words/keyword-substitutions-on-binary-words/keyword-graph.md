# Substitution graph

Let $a$ be a keyword, a binary word of length $m + 1$, and let
$n \ge 0$. The substitution graph $\mathcal{G}_n^{(a)}$ is the simple graph on the binary words of
length $n$ in which distinct words $u$ and $v$ are adjacent when $\varphi_i(u) = v$ or
$\varphi_i(v) = u$ for some $i \in \mathbb{N}$, where $\varphi_i$ is the simple map of $a$ at
letter $i$. Equivalently, $u$ and $v$ are adjacent when one is obtained from the other by
replacing an occurrence of $a$ by $\neg a$ or an occurrence of $\neg a$ by $a$, where $\neg a$ is
the letterwise negation of $a$.

## Sources

- Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 3.2 (graph structure within equivalence classes).
