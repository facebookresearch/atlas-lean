# Erdős Problem 1179 holds

For every real $\varepsilon$ with $0 < \varepsilon < 1$, the
following two bounds hold. Upper bound: there is a function $k : \mathbb{N} \to \mathbb{N}$ with
$k(N) / \log_2 N \to 1$ as $N \to \infty$ such that, for every sequence $(G_i)_{i \in \mathbb{N}}$
of finite abelian groups with $|G_i| \to \infty$, the probability that a uniformly random
$k(|G_i|)$-element subset of $G_i$ is $\varepsilon$-balanced tends to $1$ as $i \to \infty$. Lower
bound: for every finite abelian group $G$, every $\varepsilon$-balanced subset $A \subseteq G$
satisfies $|G| \le 2^{|A|}$.

Writing $g_\varepsilon(N)$ for the least size for which a uniformly random subset of a group of
order $N$ is $\varepsilon$-balanced with probability tending to $1$, Erdős and Hall proved
$g_\varepsilon(N) \le (1 + O_\varepsilon(\log \log \log N / \log \log N)) \log_2 N$, improving the
bound $(2 + o(1)) \log_2 N + O_\varepsilon(1)$ of Erdős and Rényi; the lower bound holds because
an $\varepsilon$-balanced set with $\varepsilon < 1$ has every element of $G$ as a subset sum.
erdosproblems.com/1179 lists the problem as proved.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1179, https://www.erdosproblems.com/1179 (status PROVED); resolution: P. Erdős and R. R. Hall, Probabilistic methods in group theory. II, Houston J. Math. 2 (1976), 173-180, erdosproblems.com/1179: g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N for all 0 < ε < 1.
