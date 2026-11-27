# Decay of bounded harmonic extensions of Schwartz data in a half-space

Write a point of
$\mathbb{R}^3$ as $(x, z)$ with $x = (x_1, x_2) \in \mathbb{R}^2$ and $z \in \mathbb{R}$. Let
$\phi : \mathbb{R}^2 \to \mathbb{R}$ be a Schwartz function and let
$u : \mathbb{R}^3 \to \mathbb{R}$ be harmonic at every point of the open lower half-space
$\{(x, z) : z < 0\}$, continuous on the closed lower half-space $\{(x, z) : z \le 0\}$ and bounded
there, with $u(x, 0) = \phi(x)$ for every $x \in \mathbb{R}^2$. Suppose that $u(x, z) \to 0$ as
$z \to -\infty$ uniformly in $x$: for every $\varepsilon > 0$ there is $z_0$ such that
$|u(x, z)| < \varepsilon$ for all $z \le z_0$ and all $x \in \mathbb{R}^2$. Then there is a
constant $C > 0$ such that $|u(x, z)| \le C (1 + |z|)^{-1}$ for all $z \le 0$ and all
$x \in \mathbb{R}^2$.

Boundedness of $u$ is not among the hypotheses of the source problem, but the bound fails without
it: adding to the Poisson extension of $\phi$ the harmonic function $\operatorname{Im} G(x_1 + iz)$
built from Newman's entire function $G$, which vanishes on $z = 0$ and as $z \to -\infty$ but is
unbounded near the boundary, gives a counterexample.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral, integro-differential, and pseudodifferential operators), problem `ma_proofbench_l2_72`, with the change above.
