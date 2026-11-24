# Transition function of the two-state chain

Let $\lambda_0, \lambda_1 \in \mathbb{R}$ with $\Lambda = \lambda_0 + \lambda_1 \ne 0$, and let
$\pi = (\lambda_1 / \Lambda, \lambda_0 / \Lambda)$. For every real $x$, the [transition
function](../the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md) of the two-state
generator

$$Q = \begin{pmatrix} -\lambda_0 & \lambda_0 \\ \lambda_1 & -\lambda_1 \end{pmatrix}$$

is the [sticky kernel](sticky-kernel.md) with persistence $e^{-\Lambda x}$:
$e^{xQ}(i, j) = e^{-\Lambda x} [i = j] + (1 - e^{-\Lambda x}) \pi(j)$. It is a transition probability
for $\lambda_0, \lambda_1 \ge 0$ and $x \ge 0$. The case $\Lambda = 0$ is excluded: with nonnegative
rates both rates then vanish, $Q = 0$ and $e^{xQ} = I$, while $\pi$ is not defined by the quotient.
