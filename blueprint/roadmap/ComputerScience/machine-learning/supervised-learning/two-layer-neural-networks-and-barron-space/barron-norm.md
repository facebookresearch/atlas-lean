# Barron norm

For $f : \mathbb{R}^d \to \mathbb{R}$, the Barron norm is

$$\lVert f \rVert_B = \inf_\rho \Big( \mathbb{E}_{(a, b, c) \sim \rho}\, \lvert a \rvert^2 (\lVert b \rVert_1 + \lvert c \rvert)^2 \Big)^{1/2} \in [0, \infty],$$

the infimum over the [Barron representations](is-barron-representation.md) $\rho$ of $f$ on the
cube $[0, 1]^d$, that is, the probability measures on $\mathbb{R} \times \mathbb{R}^d \times \mathbb{R}$
with $f(x) = \mathbb{E}_\rho[a \max(\langle b, x \rangle + c, 0)]$ for every $x$ in the cube; it
is $\infty$ when there is no representation. This is the $p = 2$ case of the norms
$\lVert f \rVert_{B_p} = \inf_\rho (\mathbb{E}_\rho \lvert a \rvert^p (\lVert b \rVert_1 + \lvert c \rvert)^p)^{1/p}$
of the source; for the ReLU all $p \in [1, \infty]$ give the same value (the source's
Proposition 1). The Barron space is the set of functions of finite Barron norm.

## Sources

- W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), §2.1, equation (3), and Proposition 1.
