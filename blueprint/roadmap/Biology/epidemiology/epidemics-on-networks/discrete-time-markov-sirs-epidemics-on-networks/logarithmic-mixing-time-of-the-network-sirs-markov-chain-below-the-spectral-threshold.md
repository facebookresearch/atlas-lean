# Logarithmic mixing time of the network SIRS Markov chain below the spectral threshold

**Exact chain.** Let $G$ be a connected graph on $n$ nodes with adjacency matrix $A$, largest eigenvalue $\lambda_{\max}(A)$ and neighbourhoods $N_i$. Each node is in state $\xi_i(t) \in \{0, 1, 2\}$ (susceptible, infected, recovered). Given the current configuration $X$, nodes update independently, and with $m_i = |\{j \in N_i : X_j = 1\}|$ the number of infected neighbours:

- a susceptible node becomes infected with probability $1 - (1-\beta)^{m_i}$ and otherwise stays susceptible;
- an infected node recovers with probability $\delta$ and otherwise stays infected;
- a recovered node returns to susceptible with probability $\gamma$ and otherwise stays recovered.

This defines a Markov chain on $\{0,1,2\}^n$ whose unique absorbing state is the all-susceptible configuration.

**Approximations.** The mean-field map on $(P_{R,i}, P_{I,i})_{i=1}^n$ is

$$
P_{R,i}(t+1) = (1-\gamma)P_{R,i}(t) + \delta P_{I,i}(t), \qquad P_{I,i}(t+1) = (1-\delta)P_{I,i}(t) + \Big(1 - \prod_{j\in N_i}(1 - \beta P_{I,j}(t))\Big)(1 - P_{R,i}(t) - P_{I,i}(t)),
$$

and its linearisation at the origin is $(\tilde P_R, \tilde P_I)(t+1) = \mathcal{M}(\tilde P_R, \tilde P_I)(t)$ with

$$
\mathcal{M} = \begin{pmatrix}(1-\gamma)I_n & \delta I_n \\ 0 & (1-\delta)I_n + \beta A\end{pmatrix}.
$$

**Theorem.**
1. If $\beta\lambda_{\max}(A)/\delta < 1$, the origin is a globally stable fixed point of both the linear and the nonlinear map.
2. If $\beta\lambda_{\max}(A)/\delta < 1$, the mixing time of the exact Markov chain is $O(\log n)$: the epidemic dies out quickly.
3. If $\beta\lambda_{\max}(A)/\delta > 1$, the nonlinear map has a unique nontrivial fixed point (the endemic state).

**Direct immunization.** Allow a susceptible node to become recovered (vaccinated) with probability $\theta$ per step.
- *Infection-dominant model* (a node that is both infected and vaccinated becomes infected): the disease-free fixed point of the mean-field map is locally stable if $\frac{\gamma}{\gamma+\theta}\frac{\beta}{\delta}\lambda_{\max}(A) < 1$ and globally stable if $\frac{\beta}{\delta}\lambda_{\max}(A) < 1$, and the chain mixes in $O(\log n)$ steps under the latter condition.
- *Vaccination-dominant model* (vaccination wins): local stability holds if $(1-\theta)\frac{\gamma}{\gamma+\theta}\frac{\beta}{\delta}\lambda_{\max}(A) < 1$, global stability if $(1-\theta)\frac{\beta}{\delta}\lambda_{\max}(A) < 1$, and the chain mixes in $O(\log n)$ steps under $(1-\theta)\frac{\beta\lambda_{\max}(A)}{\delta} < 1$.

So the eradication threshold is the same for the exact chain and both approximations, and a vaccine that wins over simultaneous infection relaxes it by the factor $1 - \theta$.

## Depends on

- [Spectral radius and die-out of SIS epidemics on graphs](../spectral-radius-and-die-out-of-sis-epidemics.md)

## Expansion

The matrix $\mathcal{M}$ is block upper-triangular, so its spectral radius is $\max\{1-\gamma, 1-\delta+\beta\lambda_{\max}(A)\}$, which is below $1$ exactly when $\beta\lambda_{\max}(A) < \delta$. For the exact chain, a linear-programming duality argument over all chain distributions with given marginals shows that the exact marginals obey the linear bound $p_{I,i}(t+1) \le (1-\delta)p_{I,i}(t) + \beta\sum_{j\in N_i}p_{I,j}(t)$, together with the exact recursion for $p_{R,i}$. So the vector of exact marginals is dominated componentwise by $\mathcal{M}^tp(0)$. The distance of the chain from the all-susceptible state is at most the expected number of non-susceptible nodes, $\sum_i(p_{R,i}(t) + p_{I,i}(t)) = O(n\,\rho(\mathcal{M})^t)$. This falls below any fixed constant once $t = O(\log n)$, which bounds the mixing time. The same domination, using $1 - \prod_j(1-\beta P_{I,j}) \le \beta\sum_jP_{I,j}$, gives global stability of the origin for the nonlinear map. Uniqueness of the endemic fixed point above threshold comes from a monotonicity argument for the fixed-point equations reduced to the infected coordinates. Immunization adds a $\theta$-dependent loss from the susceptible class, which rescales the infection block of the linearisation.

## Sources

- Navid Azizan Ruhi and Babak Hassibi, "SIRS Epidemics on Complex Networks: Concurrence of Exact Markov Chain and Approximated Models", arXiv:1503.07576 (2015), Section II (exact, nonlinear and linear models), Section III (Proposition III.1, Theorem III.2), Section IV (Theorem IV.1), Section V (Propositions V.1 and V.3, Theorems V.2 and V.4), <https://doi.org/10.48550/arXiv.1503.07576>. Published version: 54th IEEE Conference on Decision and Control (CDC 2015), 2919–2926, <https://doi.org/10.1109/CDC.2015.7402660>; locators above refer to the arXiv version.
