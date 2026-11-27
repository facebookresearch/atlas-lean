# Large-metapopulation limit of the incidence function model with Markovian landscape dynamics

**Model.** A metapopulation has $n$ habitat patches. Patch $i$ has a fixed location $z_i\in\Omega\subset\mathbb R^d$ and a time-varying characteristic $\theta_{i,t}\in\Theta$ that evolves as a Markov chain with common transition kernel $P$, independently of the occupancy process; the pairs $(\theta_{i,0},z_i)$ are i.i.d., locations having density $\zeta$. The characteristic determines a local survival probability $s(\theta)\in[0,1]$ and a patch weight $a(\theta)\ge0$. Given the occupancy vector $X^n_t\in\{0,1\}^n$, the characteristics and the locations, the $X^n_{i,t+1}$ are independent with

$$\mathbb P\bigl(X^n_{i,t+1}=1\mid X^n_t,\theta^n_t,z^n\bigr)=s(\theta_{i,t})X^n_{i,t}+f\Bigl(n^{-1}\sum_{j=1}^nX^n_{j,t}D(z_i,z_j)a(\theta_{j,t});\theta_{i,t}\Bigr)\bigl(1-X^n_{i,t}\bigr),$$

where $D(z,\tilde z)=e^{-\alpha\|z-\tilde z\|}$ is the dispersal kernel and $f(\cdot;\theta):[0,\infty)\to[0,1]$ the colonization function (Hanski's incidence function model is the static case). Assume the landscape chain is positive Harris recurrent and aperiodic with invariant law $\pi$ and is stationary, and let $P^\ast$ be the **dual kernel** of $P$ with respect to $\pi$: $\int_A\pi(dx)P(x,B)=\int_B\pi(dx)P^\ast(x,A)$. For a finite $\Theta$, $\pi_iP_{ij}=\pi_jP^\ast_{ji}$. (For finite $\Theta$ it suffices that the chain is irreducible, aperiodic and stationary, $\Omega$ is bounded and each $f(\cdot;\theta)$ is Lipschitz.)

**Theorem.** Suppose $\mathbb P(X^n_{i,0}=1\mid\theta_{i,0}=\theta,z_i=z)=q_0(\theta,z)$. Define recursively

$$\psi_t(z)=\int_\Omega D(z,\tilde z)\Bigl(\int_\Theta a(\theta)\,q_t(\theta,\tilde z)\,\pi(d\theta)\Bigr)\zeta(\tilde z)\,d\tilde z,$$

$$q_{t+1}(\theta,z)=\int_\Theta\Bigl[s(\eta)\,q_t(\eta,z)+f(\psi_t(z);\eta)\bigl(1-q_t(\eta,z)\bigr)\Bigr]P^\ast(\theta,d\eta).$$

1. If $X^n_{i,0}\to X_{i,0}$ in probability, then $X^n_{i,t}\to X_{i,t}$ in probability for every $t$, where $(X_{i,t},\theta_{i,t},z_i)$ is the Markov chain with $\mathbb P(X_{i,t+1}=1\mid X_{i,t},\theta_{i,t}=\theta,z_i)=s(\theta)X_{i,t}+f(\psi_t(z_i);\theta)(1-X_{i,t})$; asymptotically each patch evolves independently of the rest of the metapopulation (propagation of chaos).
2. For this limit chain, $\mathbb P(X_{i,t}=1\mid\theta_{i,t}=\theta,z_i=z)=q_t(\theta,z)$: $q_t$ is the occupancy probability of a patch at $z$ with characteristic $\theta$.
3. For every continuous $h$ on $\Theta\times\Omega$,

$$n^{-1}\sum_{i=1}^nX_{i,t}\,h(\theta_{i,t},z_i)\xrightarrow{\ p\ }\int_\Omega\int_\Theta h(\theta,z)\,q_t(\theta,z)\,\pi(d\theta)\,\zeta(z)\,dz;$$

in particular the connectivity of patch $i$ is approximated by $\psi_t(z_i)$ and the fraction of occupied patches by $\iint q_t\,d\pi\,\zeta\,dz$.

## Expansion

Positive Harris recurrence and aperiodicity give $(\theta_{i,t},z_i)\Rightarrow\pi\otimes\zeta$, so location and characteristic become asymptotically independent. The key step is a weak law of large numbers for the empirical measure $\mu_{n,t}$ of occupied patches weighted by $(\theta,z)$: if $\mu_{n,t}$ converges to a deterministic measure, the scaled connectivity $n^{-1}\sum_jX_{j,t}D(z_i,z_j)a(\theta_{j,t})$ converges in probability to a deterministic function of $z_i$, so the transition of patch $i$ decouples from the others. Induction on $t$ propagates the deterministic limit through the measure-valued recursion. The dual kernel appears because $q_t(\theta,z)$ conditions on the current characteristic: to update it one must look backwards in time to the previous characteristic, whose conditional law given $\theta_{t+1}=\theta$ under stationarity is exactly $P^\ast(\theta,\cdot)$.

## Sources

- R. McVinish, P. K. Pollett, Y. S. Chan, "A metapopulation model with Markovian landscape dynamics", arXiv (2014). Section 2 (model), Section 3 (Lemma 3.1, Theorems 3.2, 3.3, 3.4), Section 6 (Appendix A: assumptions and the measure-valued limit, Theorem 6.2), Section 7 (Appendix B: dual kernel). <https://doi.org/10.48550/arXiv.1412.0719>. Published version: Theoretical Population Biology 112 (2016), 80–96, <https://doi.org/10.1016/j.tpb.2016.08.005>; locators above refer to the arXiv version.
