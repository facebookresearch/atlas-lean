# Poisson-equation formula for steady-state parameter sensitivity

Consider a stochastic reaction network with $K$ reactions, stoichiometric vectors $\zeta_k$ and propensities $\lambda_k(x,\theta)$, modelled as a continuous-time Markov chain on a lattice state space $\mathcal E$ with generator $\mathbb Q_\theta$. Assume $\mathcal E$ is irreducible and a linear Foster–Lyapunov function $V\ge1$ certifies ergodicity, with the paper's growth conditions, so there is a unique stationary distribution $\pi_\theta$. Let $f:\mathcal E\to\mathbb R$ be an output with polynomial growth, and assume the derivatives $\partial\lambda_k/\partial\theta$ also grow polynomially. The steady-state sensitivity is $S_\theta(f)=\frac{\partial}{\partial\theta}\sum_xf(x)\pi_\theta(x)$.

**Theorem.** The Poisson equation

$$
-\mathbb Q_\theta g=f-\langle f,\pi_\theta\rangle
$$

has a solution $g$, unique up to an additive constant, and

$$
S_\theta(f)=\sum_{k=1}^K\sum_{x\in\mathcal E}\frac{\partial\lambda_k(x,\theta)}{\partial\theta}\big(g(x+\zeta_k)-g(x)\big)\,\pi_\theta(x).
$$

Steady-state sensitivities therefore need no long Monte Carlo runs. Both $\pi_\theta$ and $g$ can be approximated on finite truncations $\mathcal E_n\uparrow\mathcal E$ by the stationary finite state projection (sFSP) method. Let $\mathrm{Bdry}(\mathcal E_n)=\{x\in\mathcal E_n:\lambda_k(x)>0\text{ and }x+\zeta_k\notin\mathcal E_n\text{ for some }k\}$. If the truncations grow uniformly with respect to $V$, i.e. there is $c\in(0,1)$ with $\min_{x\in\mathrm{Bdry}(\mathcal E_n)}V(x)\ge c\max_{x\in\mathrm{Bdry}(\mathcal E_n)}V(x)$ for all $n$, then the resulting estimates converge to $S_\theta(f)$ as $n\to\infty$.

## Depends on

- [Stationary finite state projection for the chemical master equation](../stationary-finite-state-projection-for-the-chemical-master-equation.md)

## Proof sketch

Differentiate the stationarity condition $\pi_\theta\mathbb Q_\theta=0$ to get $(\partial_\theta\pi_\theta)\mathbb Q_\theta=-\pi_\theta(\partial_\theta\mathbb Q_\theta)$, and pair both sides with $g$. Because $-\mathbb Q_\theta g=f-\langle f,\pi_\theta\rangle$ and $\sum_x\partial_\theta\pi_\theta(x)=0$, the left side becomes $-S_\theta(f)$. The right side is $-\sum_x\pi_\theta(x)\sum_k\partial_\theta\lambda_k(x)\,(g(x+\zeta_k)-g(x))$. The Lyapunov conditions give the integrability needed to exchange sums and derivatives on the infinite lattice.

## Related topics

- [Stochastic reaction networks](../README.md)

## Sources

- Patrik Dürrenberger, Ankit Gupta and Mustafa Khammash, "A finite state projection method for steady-state sensitivity analysis of stochastic reaction networks", *The Journal of Chemical Physics* 150 (2019), 134101, <https://doi.org/10.1063/1.5085271>. Preprint version: arXiv:1812.04299 (2018), Assumption 2.1, Poisson equation (defn_poiss_eqn1), Theorem 3.1 (formula (exact_sens_formula)), Proposition 3.3 (convergence of the sFSP estimates under uniform growth of the truncations), <https://doi.org/10.48550/arXiv.1812.04299>.
