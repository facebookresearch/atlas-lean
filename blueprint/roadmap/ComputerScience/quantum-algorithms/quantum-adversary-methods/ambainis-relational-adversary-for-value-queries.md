# Ambainis: relational adversary bound for non-Boolean input alphabets

Let $f : D \to \beta$ with $D \subseteq \Sigma^N$, and let $R \subseteq D \times D$ relate inputs with $f(x) \ne f(y)$. Suppose every $x$ in the left projection is related to at least $m$ inputs, every $y$ in the right projection to at least $m'$ inputs, and for every related pair $(x, y)$ and index $i$ with $x_i \ne y_i$, the products $\ell_{x,i} \ell'_{y,i}$ of the numbers of partners of $x$ (resp. $y$) differing at $i$ are at most $L$. Then every $T$-query value-oracle algorithm computing $f$ with error $\varepsilon$ satisfies

$$\big(1 - 2\sqrt{\varepsilon(1 - \varepsilon)}\big)\sqrt{m m'} \le 2T\sqrt{L}.$$

This holds for arbitrary unitary oracle families $\mathrm{step} : \Sigma \to U(\mathbb{C}^V)$ and multi-outcome classical readouts, with the exact constant $2$.

## Proof sketch

Track the weighted progress $W_t = \sum_{(x,y) \in R} w_{xy}|\langle\psi^x_t, \psi^y_t\rangle|$. Initially the states coincide; at the end, distinguishing $f(x) \ne f(y)$ with error $\varepsilon$ forces $|\langle \psi^x_T, \psi^y_T\rangle| \le 2\sqrt{\varepsilon(1-\varepsilon)}$. One query changes the inner product only through the query-register amplitude on indices where $x_i \ne y_i$, and Cauchy–Schwarz with the counting parameters bounds the change per query by $2\sqrt{L}/\sqrt{mm'}$ of the total weight.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)
- [Ambainis adversary bound](../quantum-query-lower-bounds/ambainis-adversary-bound.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002.
