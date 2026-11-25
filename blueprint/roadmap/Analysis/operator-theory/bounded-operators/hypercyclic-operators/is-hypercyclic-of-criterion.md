# Hypercyclicity criterion

Let $\mathbb{k}$ be a nontrivially normed field and $E$ a normed space over $\mathbb{k}$ that is a Baire space (for instance a Banach space) and has a countable dense subset. Let $T$ be a bounded operator on $E$, let $(n_k)$ be a sequence of natural numbers with $n_k \to \infty$, let $X_0, Y_0 \subseteq E$ be dense, and let $S_k : E \to E$ be maps such that

- $T^{n_k} x \to 0$ for every $x \in X_0$,
- $S_k y \to 0$ for every $y \in Y_0$, and
- $T^{n_k} S_k y \to y$ for every $y \in Y_0$.

Then $T$ is [hypercyclic](is-hypercyclic.md). The Baire category proof combines the three estimates and uses $n_k \to \infty$ to meet each ball of a countable base after every prescribed time. The case $n_k = k$ with $T^k S_k y = y$ exactly on $Y_0$ is included.
