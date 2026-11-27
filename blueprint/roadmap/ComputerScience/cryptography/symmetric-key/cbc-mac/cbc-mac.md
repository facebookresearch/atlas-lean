# Basic CBC-MAC

Let $X$ be an additive commutative group and $p : X \to X$ an arbitrary map. The basic CBC-MAC of an $\ell$-block message $m \in X^\ell$ is the [CBC-MAC chaining](cbc-mac-from.md) started at $0$:

$$
t_0 = 0, \qquad t_i = p(t_{i-1} + m_i), \qquad \text{tag} = t_\ell .
$$

For $\ell \ge 1$ this is the last block of CBC encryption with the all-zero initial vector. At $\ell = 0$ the tag is $0$ for the (unique) empty message. Katz and Lindell, 2nd ed., Construction 4.11, uses a keyed function $F_k$ and a positive length $\ell$; the definition here extends it to $\ell = 0$ and to an arbitrary map $p$.
