# CBC encryption

Let $X$ be an additive commutative group of blocks and $p \colon X \to X$ an arbitrary function. For a message $m \in X^\ell$ and an initial vector $\mathrm{iv} \in X$, CBC encryption returns $(\mathrm{iv}, c_1, \dots, c_\ell)$ with the [chain](cbc-chain.md)

$$
c_1 = p(\mathrm{iv} + m_1), \qquad c_i = p(c_{i-1} + m_i) \quad (1 < i \le \ell),
$$

and with the empty chain for $\ell = 0$ (Katz and Lindell, Section 3.6.2, with XOR replaced by the group addition).
