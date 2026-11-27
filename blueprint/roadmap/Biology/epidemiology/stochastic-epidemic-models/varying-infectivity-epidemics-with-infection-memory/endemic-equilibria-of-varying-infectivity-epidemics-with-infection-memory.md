# Endemic equilibria of varying-infectivity epidemics with infection memory

**Setting.** A population of $N$ individuals is followed as a piecewise deterministic Markov process. Each individual carries a *trait* $\theta\in\Theta\subseteq\mathbb R^d$ (for example the strain or immune profile of its last infection) and an age of infection $a\ge0$ (time since that infection). Its infectivity is $\lambda(a,\theta)$ and its susceptibility is $\gamma(a,\theta)$: infectiousness first rises and falls, then immunity wanes and susceptibility recovers. At each new infection of an individual whose current trait is $\tilde\theta$, its age resets to $0$ and a new trait is drawn from the kernel $K(\tilde\theta,\theta)\,\nu(d\theta)$, where $\nu$ is a $\sigma$-finite measure and $\int_\Theta K(\tilde\theta,\theta)\nu(d\theta)=1$; this is the *memory of the last infection* (antigenic drift, immune maturation). The assumptions include: $0\le\lambda\le\lambda_*$, $0\le\gamma\le1$, $\gamma(0,\cdot)=0$, infectivity and susceptibility have disjoint supports in $a$ (no reinfection while infectious), the long-run mean susceptibility $\gamma_*(\theta)=\lim_{a\to\infty}a^{-1}\int_0^a\gamma(s,\theta)\,ds$ exists and is positive, and $K>0$ with a mild integrability condition. $T_I(\theta)$ denotes the infectious period. The empirical measure $\mu^N_t$ of (age, trait) pairs describes the population state.

**Theorem 3.1 (law of large numbers).** As $N\to\infty$, $\mu^N$ converges in law in the Skorokhod space of probability-measure-valued paths to the unique solution $\mu$ of a measure-valued equation, equivalently of an age-structured transport PDE with renewal boundary condition driven by the force of infection $\mathfrak F(t)=\int\lambda(a,\theta)\mu_t(da,d\theta)$ (Proposition 4.1, Corollary 4.2).

**Theorem 3.3 (endemic equilibrium).** There is a unique $\mathfrak S_*\in L^1(\nu)$, positive $\nu$-a.e., solving $\mathfrak S_*(\theta)=\int_\Theta K(\tilde\theta,\theta)\mathfrak S_*(\tilde\theta)\nu(d\tilde\theta)$ with $\int\lambda(a,\theta)\mathfrak S_*(\theta)\,da\,\nu(d\theta)=1$. An endemic equilibrium exists when

$$\int_\Theta\frac{\mathfrak S_*(\theta)}{\gamma_*(\theta)}\,\nu(d\theta)<1,$$

with endemic infected proportion $I_*=\mathfrak F_*\int_\Theta T_I(\theta)\mathfrak S_*(\theta)\nu(d\theta)$, $\mathfrak F_*$ the equilibrium force of infection. If moreover $\gamma(a,\cdot)\ge a^{-1}\int_0^a\gamma(s,\cdot)ds$ for all $a$ (susceptibility at least its running mean), the endemic equilibrium is unique, and when the integral exceeds $1$ the only equilibrium is disease-free.

## Expansion

At equilibrium the force of infection is constant, so each individual alternates infections in a renewal fashion, with trait sequence a Markov chain driven by $K$. The stationary trait distribution is the Perron eigenfunction of the integral operator with kernel $K$, which has spectral radius $1$ by a Krein-Rutman-type theorem for positive integral operators with a compact power (Theorem 5.1, Proposition 5.2). Solving for the constant force of infection reduces to a scalar equation whose left side moves monotonically under the running-mean condition; the condition $\int\mathfrak S_*/\gamma_*<1$ says that, averaged over traits, the long-run waiting time to reinfection is short enough for infection to persist. The model covers vaccination policies by letting vaccination reset susceptibility (Section 6).

## Sources

- H. Guérin, A. B. Zotsa-Ngoufack, "A stochastic epidemic model with memory of the last infection and waning immunity", *SIAM Journal on Applied Mathematics* 86(5) (2026), 2615–2647, Theorem 3.1, Theorem 3.3, Proposition 4.1, Corollary 4.2, Proposition 5.2, <https://doi.org/10.1137/25m1757940> (preprint arXiv:2505.00601).
