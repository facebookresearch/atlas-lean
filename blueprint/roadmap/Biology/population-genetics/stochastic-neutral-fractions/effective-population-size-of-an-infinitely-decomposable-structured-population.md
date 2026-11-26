# Effective population size of an infinitely decomposable structured population

**Model.** A population with ecological types $x \in E$ (finite) follows the SDE $dV_t = b(V_t)\,dt + N^{-1/2} a(V_t)\,dW_t$ on $\mathbb{R}^E$. It is *$\infty$-decomposable*: there are $F(v) \in \mathbb{R}^{E\times E}$ and $C(v) \in \mathbb{R}^{(E\times E)\times E}$ with

$$b(v) = F(v)v, \qquad aa^*(v) = C(v)v, \qquad \sigma(v,w)\sigma^*(v,w) = C(v)w .$$

$F(v)_{xy}$ is the rate at which a type-$y$ individual produces type-$x$ offspring and $C_{xy,z}(v)$ the covariance of type-$x$ and type-$y$ offspring numbers of one type-$z$ individual. The $K$ *stochastic neutral fractions* $U^{N,1},\dots,U^{N,K}$ (allelic components) solve

$$dU^{N,k}_t = F\Bigl(\sum_j U^{N,j}_t\Bigr)U^{N,k}_t\,dt + \frac{1}{\sqrt N}\,\sigma\Bigl(\sum_j U^{N,j}_t,\ U^{N,k}_t\Bigr)dW^k_t ,$$

with independent Brownian motions $W^k$, so that $\sum_k U^{N,k}$ solves the original SDE.

**Quantities.** Let $\tilde h$ be the stable equilibrium of the deterministic flow $\dot v = F(v)v$ and $h$ the associated left eigenvector (reproductive values), normalized by $\langle h, \tilde h\rangle = 1$. Set $\Pi_x = \tilde h_x h_x$,

$$n_e(x,y) = \Bigl(\frac{1}{\tilde h_x\tilde h_y}\sum_z C(\tilde h)_{xy,z}\tilde h_z\Bigr)^{-1}, \qquad \Sigma^2 = \langle h, aa^*(\tilde h)h\rangle = \sum_{x,y}\frac{\Pi_x\Pi_y}{n_e(x,y)} .$$

**Theorem.** For a fixed non-negative initial condition $U_0$ in the basin of $\tilde h$,

$$\bigl(U^N_{tN/\Sigma^2}\bigr)_{t\in(0,T]} \Longrightarrow \bigl(\theta_t \otimes \tilde h\bigr)_{t \in (0,T]} ,$$

where $(\theta\otimes \tilde h)_{xj} = \tilde h_x\theta^j$ and $\theta$ is a standard $(K-1)$-dimensional Wright-Fisher diffusion started from $\pi^j(U_0)/\tilde h$, $\pi^j$ being the $t\to\infty$ limit of $\dot\pi_t = F(v_t)\pi_t$, $\pi_0 = U^j_0$, driven by $\dot v_t = F(v_t)v_t$, $v_0 = \sum_j U_0^j$. The structured population therefore behaves like a Wright-Fisher population with

$$N_e = \frac{N}{\Sigma^2}.$$

Only the drift decomposition $F$ enters the limit; the choice of $(\sigma, C)$ does not, but different $F$ compatible with the same $b$ can give different neutral fractions.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](../effective-population-size/effective-population-size-definitions.md)

## Expansion

On the fast time scale the deterministic drift pulls every neutral fraction onto the line through $\tilde h$, so the state collapses onto the simplex $\Gamma^K = \{\theta\otimes\tilde h\}$. The slow coordinates are the reproductive-value-weighted masses $\langle h, U^k\rangle$, which have zero drift on $\Gamma^K$; their quadratic variation, computed with the decomposability identity, is $\Sigma^2\theta^k(\delta_{kl} - \theta^l)/N$, i.e. Wright-Fisher noise at rate $\Sigma^2/N$. Katzenberger's small-noise projection theorem makes this rigorous. $\Pi_x$ is the stationary ancestral lineage distribution, and $n_e(x,y)$ is the local effective size felt by two lineages at $x$ and $y$.

## Sources

- R. Forien, E. Schertzer, Z. Talyigás, J. Tourniaire, "Stochastic neutral fractions and the effective population size" (2025), Assumption on $\infty$-decomposability, Eq. (Sigma-ancestral), Theorem 3 and Proposition 7, <https://doi.org/10.48550/arXiv.2502.05062>.
