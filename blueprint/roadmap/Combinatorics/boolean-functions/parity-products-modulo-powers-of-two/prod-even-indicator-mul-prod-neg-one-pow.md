# Truncated subset expansion of parity products modulo powers of two

Let $E$ be a set, $r$ a natural number, $J_1$ and $J_2$ disjoint subsets of $\{0, \dots, r-1\}$, and $(A_j)_{j < r}$ finite subsets of $E$. Let $\nu$ and $M$ be natural numbers with $\nu \ge 1$ and $\nu - 1 + \lvert J_1\rvert \le M$. Then

$$\prod_{j \in J_1} \varepsilon(\lvert A_j\rvert) \prod_{j \in J_2} (-1)^{\lvert A_j\rvert} \equiv \sum_{S} \prod_{j \in J_1} c_{\lvert S_j\rvert} \prod_{j \in J_2} (-2)^{\lvert S_j\rvert} \pmod{2^\nu},$$

where $\varepsilon$ is the [even indicator](even-indicator.md), $c_i$ are the [parity coefficients](parity-coeff.md), and the sum runs over the tuples $S = (S_j)_{j < r}$ with $S_j \subseteq A_j$ for $j \in J_1 \cup J_2$, $S_j = \emptyset$ for the other $j$, and $\sum_j \lvert S_j\rvert \le M$. Each even-indicator factor costs at most one power of $2$, which is why the cutoff $M$ must be at least $\nu - 1 + \lvert J_1\rvert$.
