# Fano-factor bounds for feedback-regulated burst networks

**Model.** A network of $N$ molecular species $X=(X_1,\dots,X_N)$ evolves as a continuous-time Markov chain: species $i$ is produced in bursts at the state-dependent rate $f_i(X_{-i})$ (depending on the other species), each burst adding an independent positive integer number $K_i$ of molecules with $\kappa_i=\mathbb{E}K_i$ and $\mathbb{E}K_i^2<\infty$, and each molecule degrades independently at rate $1/\tau_i$. Assume the chain is irreducible with a stationary distribution $\pi$ having finite second moments. The stationary Fano factor is $F_{X_i}=\mathrm{Var}_\pi(X_i)/\mathbb{E}_\pi X_i$; for constant production it equals the *burst baseline*

$$B_i = \frac{\mathbb{E}K_i^2+\mathbb{E}K_i}{2\,\mathbb{E}K_i},$$

which is $1$ for unit births and $\kappa_i$ for geometric bursts $\mathbb{P}(K_i=k)=p_i(1-p_i)^{k-1}$, $k\ge1$.

**Theorem.**

1. (*Geometric bursts.*) If every $K_i$ is positive geometric, then for arbitrary production rates $f_i$,

$$\sum_{i=1}^N \frac{F_{X_i}-\kappa_i}{\tau_i\,\kappa_i} \ge 0,$$

so feedback cannot push every component below its baseline: if one component lies below $\kappa_i$, another must lie above.
2. (*Sign-consistent regulation.*) For arbitrary positive integer burst laws with finite second moment, if each $f_i$ is monotone in each argument and every cycle of the regulatory interaction graph contains an even number of inhibitory interactions, then $\mathrm{Cov}_\pi(f_i(X_{-i}),X_i)\ge0$ and $F_{X_i}\ge B_i$ for every $i$.
3. (*Counterexample.*) Without these restrictions the bound fails: there is a two-component network with bounded production rates and burst sizes in $\{1,2\}$ in which both stationary Fano factors lie strictly below their common baseline.

## Expansion

Stationary moment identities express $F_{X_i}-B_i$ through the covariance between the production rate of $i$ and $X_i$ itself; under sign consistency the burst semigroup is monotone for a signed partial order, and association (an FKG-type inequality) makes that covariance nonnegative. For geometric bursts an information inequality bounds a componentwise Fisher-information rate by $(F_{X_i}-\kappa_i)/(\tau_i\kappa_i)$, and these rates sum to a nonnegative total. The counterexample is a small perturbation of a constant-rate model with an explicit second-order expansion of the Fano factors.

## Sources

- D. F. Anderson, "Fluctuation impossibility results for stochastic burst networks", arXiv:2607.20823, Theorems 1–2 and the two-component counterexample. <https://doi.org/10.48550/arXiv.2607.20823>
