# Cbc Mac List

Let $X$ be an additive commutative group and $p : X \to X$ an arbitrary map. For a list $m = [m_1, \dots, m_n]$ of blocks of any length, the CBC-MAC chaining is the left fold of $t \mapsto p(t + x)$ over $m$ starting at $0$:

$$
t_0 = 0, \qquad t_i = p(t_{i-1} + m_i), \qquad \text{value} = t_n .
$$

The empty list gives $0$.
