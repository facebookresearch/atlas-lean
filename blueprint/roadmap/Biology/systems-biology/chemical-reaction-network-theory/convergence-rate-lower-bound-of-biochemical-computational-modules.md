# Convergence rate lower bound of biochemical computational modules

**Setting.** A mass-action system on species $X_1, \dots, X_n$ evolves by $\dot x = \Gamma \mathscr K(x)$ on $\mathbb{R}^n_{\ge 0}$, where $\Gamma$ is the stoichiometric matrix and $\mathscr K_j(x) = k_j \prod_i x_i^{v_{ij}}$ with rate constants $k_j > 0$. A **biochemical computational module** splits the species into inputs $x_1 \in \mathbb{R}^{n_1}_{\ge 0}$ and outputs $x_2 \in \mathbb{R}^{n_2}_{\ge 0}$, $\dot x_1 = f_1(x_1, x_2)$, $\dot x_2 = f_2(x_1, x_2)$, and computes $g$ if the trajectory converges to a limiting steady state $\bar x$ with $\bar x_2 = g(x_1(0))$. Its **convergence rate** is

$$\rho = -\limsup_{t \to \infty} \frac{\ln \|x(t) - \bar x\|}{t}.$$

If $\|x(t) - \bar x\| \le M t^{a} e^{-\rho t}$ for some $M, a > 0$, the module computes $g$ at rate at least $\rho$; conversely a rate exceeding $\rho$ gives $\|x(t) - \bar x\| \le M e^{-\rho t}$, so the time to reach accuracy $\epsilon$ is at most $\rho^{-1}\ln(M/\epsilon)$.

**Statement.**

1. (Linear modules.) If all reactions are inflows, outflows or have a single non-catalytic reactant, the dynamics are affine, $\dot x = Ax + u$. If $A$ is Hurwitz with eigenvalues $\operatorname{Re}\lambda_n \le \dots \le \operatorname{Re}\lambda_1 < 0$, the module computes the output block $g(x_1(0)) = \bar x_2$ of its unique, globally asymptotically stable equilibrium $\bar x$ with convergence rate at least $|\operatorname{Re}\lambda_1|$.
2. (Nonlinear modules.) If a general mass-action module has an asymptotically stable equilibrium $\bar x$ whose Jacobian has eigenvalues $\operatorname{Re}\lambda_n \le \dots \le \operatorname{Re}\lambda_1 < 0$, then for trajectories converging to $\bar x$ the rate of computing $g(x_1(0)) = \bar x_2$ is at least $|\operatorname{Re}\lambda_1|$, the modulus of the real part of the dominant eigenvalue.

## Depends on

- [CRNs as computing devices](../crns-as-computing-devices.md)

## Expansion

For the affine case $x(t) - \bar x = e^{At}(x(0) - \bar x)$, and the Jordan form of $A$ gives $\|e^{At}\| \le M t^{a} e^{\operatorname{Re}\lambda_1 t}$ with $a$ one less than the largest Jordan block size for $\lambda_1$. In the nonlinear case write $\dot y = Jy + h(y)$ with $y = x - \bar x$; the polynomial remainder satisfies $\|h(y)\| \le c\|y\|^{p}$ with $p > 1$ near $0$. Approximating $J$ by a diagonalizable matrix with eigenvalues within $\epsilon$ and applying a Gronwall argument in its eigenbasis gives $\|y(t)\| \le M e^{-(|\operatorname{Re}\lambda_1| - \epsilon)t}$ once the trajectory is close to $\bar x$; letting $\epsilon \to 0$ yields the bound on $\rho$.

## Sources

- Y. Fan, C. Gao, S. He and J. Chen, On the convergence rate lower bound of biochemical computational modules, arXiv (2026). <https://doi.org/10.48550/arXiv.2608.12109> (Definition 4, Lemma 5, Proposition 6, Theorem 7; appendix Lemmas 8 and 9.)
