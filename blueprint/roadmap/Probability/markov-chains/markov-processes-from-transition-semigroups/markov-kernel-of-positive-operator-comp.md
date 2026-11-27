# Operator composition corresponds to kernel composition

Let $E$ be a compact metrizable space with its Borel $\sigma$-algebra and $T, U$ positive continuous
linear operators on $C(E, \mathbb{R})$ with $T1 = U1 = 1$, with [Markov
kernels](markov-kernel-of-positive-operator.md) $K_T$ and $K_U$. Then the Markov kernel of
$T \circ U$ ($f \mapsto T(Uf)$) is the composite kernel that first uses $K_T$ and then $K_U$:

$$K_{T \circ U}(x, A) = \int_E K_T(x, dy)\, K_U(y, A) .$$
