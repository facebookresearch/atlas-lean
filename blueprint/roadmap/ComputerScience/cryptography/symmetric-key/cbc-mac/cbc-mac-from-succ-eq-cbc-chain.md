# Cbc Mac From succ eq cbc Chain

Let $X$ be an additive commutative group and $p : X \to X$ an arbitrary map. For every $n$, every starting value $a \in X$ and every message $m$ of $n + 1$ blocks, the CBC-MAC chaining from $a$ (see [CBC-MAC chaining from a value](cbc-mac-from.md)) equals the last coordinate, at index $n + 1$ in one-based numbering, of the [CBC chain](../modes-of-operation-counter-mode-and-cbc/cbc-chain.md) of $m$ under $p$ with the **same** initial value $a$:

$$
c_1 = p(a + m_1), \qquad c_i = p(c_{i-1} + m_i), \qquad \text{value} = c_{n+1}.
$$

The statement needs at least one block: on the empty message the chaining returns $a$ and the CBC chain has no coordinates.
