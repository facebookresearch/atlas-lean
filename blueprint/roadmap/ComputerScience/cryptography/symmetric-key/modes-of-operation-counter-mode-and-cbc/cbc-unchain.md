# CBC unchaining

Let $X$ be an additive commutative group and let $p' \colon X \to X$ be **any** function. Unchaining $c \in X^n$ from the initial value $\mathrm{iv}$ returns $m \in X^n$ with

$$
m_i = p'(c_i) - c_{i-1} \quad (1 \le i \le n), \qquad c_0 = \mathrm{iv};
$$

for $n = 0$ it returns the empty vector. No inverse relation between $p'$ and a chaining permutation is assumed; with $p'$ the inverse of the block cipher this undoes the CBC chain (see [unchaining inverts chaining](cbc-unchain-cbc-chain.md)).
