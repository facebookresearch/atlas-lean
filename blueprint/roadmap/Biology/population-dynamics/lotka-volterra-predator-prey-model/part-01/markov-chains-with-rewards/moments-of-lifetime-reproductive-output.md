# Moments of lifetime reproductive output in a Markov chain with rewards

**Setting.** An individual life cycle is a finite-state, discrete-time absorbing Markov chain with $\tau$ transient (living) states and $\alpha$ absorbing (dead) states, $s = \tau + \alpha$. Its column-stochastic transition matrix is

$$P = \begin{pmatrix} U & 0 \\ M & I_\alpha \end{pmatrix},$$

where $U$ ($\tau \times \tau$) holds the transition probabilities among living states, $M$ ($\alpha \times \tau$) the probabilities of dying from each living state, and the spectral radius of $U$ is strictly less than $1$, so death occurs with probability $1$. Every transition $j \to i$ out of a living state $j$ carries a random reproductive *reward* $r_{ij}$ (offspring produced on that step), drawn independently of everything else given the transition; the dead accumulate nothing. Let $R_k$ be the $s \times s$ matrix with entries $(R_k)_{ij} = \mathbb E[r_{ij}^k]$, let $Z = (I_\tau \ \ 0_{\tau \times \alpha})$, let $\tilde R_k = Z R_k Z^{\mathsf T}$ be its living-to-living block, let $N = (I_\tau - U)^{-1}$ be the fundamental matrix, and let $\circ$ denote the entrywise product. The *lifetime reproductive output* (LRO) of an individual is the sum of the rewards it collects until absorption; write $\tilde\rho_k$ for the $\tau$-vector whose $j$-th entry is the $k$-th moment of the remaining LRO of an individual currently in living state $j$.

**Theorem.** For every $m \ge 1$,

$$\tilde\rho_1 = N^{\mathsf T} Z\,(P \circ R_1)^{\mathsf T} \mathbf 1_s,$$

$$\tilde\rho_m = N^{\mathsf T}\Big[ Z\,(P \circ R_m)^{\mathsf T} \mathbf 1_s + \sum_{k=1}^{m-1} \binom{m}{k} \big(U \circ \tilde R_{m-k}\big)^{\mathsf T} \tilde\rho_k \Big].$$

Consequently the variance, coefficient of variation and Crow's opportunity for selection of LRO, for each starting state, are

$$V = \tilde\rho_2 - \tilde\rho_1 \circ \tilde\rho_1, \qquad \mathrm{CV} = D(\tilde\rho_1)^{-1} \sqrt{V}, \qquad I = \mathrm{CV} \circ \mathrm{CV},$$

with $D(x)$ the diagonal matrix of $x$ and the square root taken entrywise, and the skewness is $\mathrm{Sk} = (\tilde\rho_3 - 3\tilde\rho_2\circ\tilde\rho_1 + 2\tilde\rho_1^{\circ 3}) \circ V^{\circ(-3/2)}$, entrywise. If the life cycle has a single offspring stage, state $1$ ($A = U + F$ with $F = e_1 f^{\mathsf T}$), and the rewards count offspring, $R_1 = \mathbf 1_s (f^{\mathsf T}\ \ 0_{1 \times \alpha})$, then the first moment of LRO from the newborn state is the net reproductive rate $R_0 = \rho\big(F(I - U)^{-1}\big)$: $\tilde\rho_1 = N^{\mathsf T} f$ and $(\tilde\rho_1)_1 = f^{\mathsf T} N e_1 = \rho(FN)$. With several offspring stages, or rewards in another currency, the two differ in general.

## Expansion

First-step analysis. An individual in living state $j$ moves to state $i$ with probability $P_{ij}$, collects $r_{ij}$, and then has remaining LRO $\rho'$ distributed as that of a fresh individual in $i$ (zero if $i$ is dead), independent of $r_{ij}$. Expanding $\mathbb E[(r_{ij} + \rho')^m] = \sum_{k=0}^{m} \binom{m}{k} \mathbb E[r_{ij}^{m-k}]\,\mathbb E[\rho'^k]$ and averaging over $i$ gives

$$\tilde\rho_m = Z (P \circ R_m)^{\mathsf T} \mathbf 1_s + \sum_{k=1}^{m-1} \binom{m}{k} (U \circ \tilde R_{m-k})^{\mathsf T} \tilde\rho_k + U^{\mathsf T} \tilde\rho_m,$$

where the $k = 0$ term is the pure reward moment and the $k = m$ term uses $\mathbb E[r^0] = 1$ over living destinations. Since $\rho(U) < 1$, $I - U^{\mathsf T}$ is invertible with inverse $N^{\mathsf T}$, which yields the closed form; moments are computed recursively in $m$. Unlike earlier iterative schemes, this is an exact closed form for every moment, and it applies to any age- or stage-classified matrix model $A = U + F$ once reward moments are specified (for stage-specific mean fertility $f$, $R_1 = \mathbf 1_s (f^{\mathsf T}\ \ 0_{1 \times \alpha})$).

## Sources

- H. Caswell, "Beyond R0: demographic models for variability of lifetime reproductive output", PLoS ONE 6(6) (2011) e20809, section "Analysis" (convergence of the accumulated-reward moments to lifetime moments as the time to the terminal time grows) and Proposition 1, Eqs. (10)–(13), the case of one absorbing state, <https://doi.org/10.1371/journal.pone.0020809>, PMCID PMC3126812.
- S. F. van Daalen and H. Caswell, "Lifetime reproductive output: individual stochasticity, variance, and sensitivity analysis", *Theoretical Ecology* 10 (2017) 355–374, Section "The statistics of LRO", Theorem 1, Eqs. (2)–(4), (10)–(24). <https://doi.org/10.1007/s12080-017-0335-2> (PMC6979506)
