# Barron representation

A measure $\rho$ on the parameters $(a, b, c) \in \mathbb{R} \times \mathbb{R}^d \times \mathbb{R}$
represents $f : \mathbb{R}^d \to \mathbb{R}$ on the [cube](unit-cube.md) when $\rho$ is a
probability measure and, for every $x \in [0, 1]^d$, the neuron output
$(a, b, c) \mapsto a \max(\langle b, x \rangle + c, 0)$ is $\rho$-integrable with
$f(x) = \int a \max(\langle b, x \rangle + c, 0) \, d\rho(a, b, c)$ (E, Ma and Wu, *The Barron space
and the flow-induced function spaces for neural network models*, equation (1)).
