# Law of large numbers for a spatial SIR epidemic with varying infectivity on an unbounded domain

**Model.** $N$ individuals sit at fixed positions $X^1,\dots,X^N$ in a closed set $D \subseteq \mathbb{R}^d$ (possibly unbounded) and are susceptible, infected or recovered. The $j$-th infected individual has a random infectivity $\lambda_j(t)$ at time $t$ after its infection, i.i.d. across individuals, with $0 \le \lambda_j \le \lambda^*$, mean $\bar\lambda(t)$ (and $\bar\lambda^0(t)$ for those initially infected), infectious period $\eta_j = \sup\{t : \lambda_j(t) > 0\}$ with distribution function $F$ (resp. $F_0$), $F^c = 1 - F$. For a symmetric kernel $K \ge 0$ and $\gamma \in [0,1)$, a susceptible at $X^i$ is infected at rate

$$
\frac{1}{N^{1-\gamma}}\sum_{j \text{ infected}} \frac{K(X^i,X^j)}{\bigl[\sum_{\ell=1}^N K(X^\ell,X^j)\bigr]^{\gamma}}\,\lambda_j(t - \tau_j),
$$

where $\tau_j$ is the infection time of $j$ (so $\gamma < 1$ increases transmission in dense regions). Let $\bar\mu^{S,N}_t, \bar\mu^{I,N}_t, \bar\mu^{R,N}_t$ be the empirical measures of susceptible, infected and recovered positions divided by $N$, and $\bar\mu^{\mathfrak{F},N}_t = \frac1N\sum_j \lambda_j(t - \tau_j)\delta_{X^j}$ the force-of-infection measure.

**Assumptions.** Initial states and positions are i.i.d., with initial fractions converging to $\bar S(0),\bar I(0),\bar R(0)$ and positions of each type having densities $\pi_S,\pi_I,\pi_R$, so the population density is $\bar\mu(x) = \bar S(0)\pi_S(x) + \bar I(0)\pi_I(x) + \bar R(0)\pi_R(x)$. The kernel is bounded, bounded below by $\underline{c} > 0$ at distance $\le r$, and zero at distance $> \underline{R}$. The density has stretched-exponential tails, $c_0 e^{-a\|x\|^{\delta}} \le \bar\mu(x) \le C_0 e^{-a\|x\|^{\delta}}$, and $D$ satisfies an interior cone condition.

**Statement.** As $N \to \infty$, $(\bar\mu^{S,N}, \bar\mu^{\mathfrak{F},N}, \bar\mu^{I,N}, \bar\mu^{R,N})$ converges in probability in the Skorokhod space of measure-valued paths to the unique solution, absolutely continuous with respect to $\bar\mu$, whose densities $S, \mathfrak{F}, I, R$ satisfy

$$
\begin{aligned}
S(t,x) &= S(0,x) - \int_0^t S(s,x)\int_D \Lambda(x,y)\,\mathfrak{F}(s,y)\,dy\,ds,\\
\mathfrak{F}(t,x) &= \bar\lambda^0(t) I(0,x) + \int_0^t \bar\lambda(t-s)\, S(s,x)\int_D \Lambda(x,y)\,\mathfrak{F}(s,y)\,dy\,ds,\\
I(t,x) &= I(0,x)F_0^c(t) + \int_0^t F^c(t-s)\, S(s,x)\int_D \Lambda(x,y)\,\mathfrak{F}(s,y)\,dy\,ds,\\
R(t,x) &= R(0,x) + I(0,x)F_0(t) + \int_0^t F(t-s)\, S(s,x)\int_D \Lambda(x,y)\,\mathfrak{F}(s,y)\,dy\,ds,
\end{aligned}
\qquad
\Lambda(x,y) = \frac{K(x,y)\,\bar\mu(y)}{\bigl[\int_D K(z,y)\,\bar\mu(z)\,dz\bigr]^{\gamma}} .
$$

This is a spatial, non-Markovian Kermack–McKendrick system: the force of infection at $x$ is a kernel average of the age-of-infection-weighted infectivity of earlier infections.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The key estimate is that $\varphi \mapsto \int_D \Lambda(\cdot,y)\varphi(y)\,dy$ is bounded on $L^\infty$. The normalizing denominator can be small where the population is sparse, but the cone condition and the tail bounds give $\int_D K(z,y)\bar\mu(z)dz \gtrsim e^{-a(1+\epsilon)\|y\|^\delta}$, so the integrand is at most $e^{-a(1 - \gamma(1+\epsilon))\|y\|^\delta}$, integrable when $\gamma < 1$; this is why $\gamma = 1$ is excluded on unbounded domains. With this bound the limit system has at most one solution by a Gronwall argument in $L^1(\bar\mu)$. The proof truncates to bounded domains $D_n = D \cap B(0,M_n)$, where the bounded-domain law of large numbers applies, and shows the truncated limits converge to the full system as $n \to \infty$.

## Sources

- A. Kanga and E. Pardoux, Spatial SIR epidemic model with varying infectivity in an unbounded domain: law of large numbers, arXiv:2511.12350 (2025), Section 2, Assumptions 3.1–3.2, Theorem 3.1 and Proposition 3.1, <https://doi.org/10.48550/arXiv.2511.12350>.
