# Ranks are independent of the order statistics

Let $n \in \mathbb{N}$ and let $X_0, \dots, X_{n-1}$ be independent real random variables on a probability space $(\Omega, \mu)$, each with law $\nu$, a probability measure on $\mathbb{R}$ without atoms ($\nu(\{x\}) = 0$ for every $x \in \mathbb{R}$). The rank of $X_i$ in the sample is the competition rank $R_i = 1 + \#\{j : X_j < X_i\}$; tied observations would share the smallest rank of their group, but by the absence of atoms ties occur with probability $0$. Let $X_{(0)} \le X_{(1)} \le \dots \le X_{(n-1)}$ be the order statistics, the sample sorted in nondecreasing order with repeated values counted with multiplicity. Then the rank vector $(R_0, \dots, R_{n-1})$ and the vector of order statistics $(X_{(0)}, \dots, X_{(n-1)})$ are independent random variables.

## Sources

- J. Hájek, Z. Šidák and P. K. Sen, *Theory of Rank Tests*, 2nd ed., Academic Press (1999).
