# Poisson limit for fixation times of beneficial mutations in a Moran model with weak clonal interference

**Model.** A population of fixed size $N$ evolves in continuous time. Each individual carries a number $k \ge 0$ of beneficial mutations and has fitness $(1+s_N)^k$. Each individual dies at rate $1$ and is replaced by the offspring of an individual chosen with probability proportional to fitness; independently of reproduction, each individual acquires one additional beneficial mutation at the times of a homogeneous Poisson process of rate $\mu_N$ during its life, and offspring inherit their parent's mutations (unlimited supply of beneficial mutations). Let $X_{k,N}(t)$ be the number of individuals with exactly $k$ mutations, $T_{0,N} = 0$ and

$$T_{k,N} = \inf\Big\{t \ge 0 : X_{k,N}(t) > \frac{\log N}{s_N}\Big\},$$

the time at which type $k$ becomes established. Assume

$$0 < \mu_N \ll \frac{1}{N\log N}, \qquad N^{-\eta} \ll s_N \ll 1 \ \text{ for some } \eta < 1.$$

**Theorem.** Let $\xi_1, \xi_2, \dots$ be i.i.d. exponential random variables with mean $1$. For each fixed $K$, as $N \to \infty$,

$$\big(N\mu_N s_N\,(T_{k,N} - T_{k-1,N})\big)_{k=1}^K \Rightarrow (\xi_k)_{k=1}^K.$$

Moreover there are constants $C_1, C_2$ depending on $\eta$ such that for every $k \ge 0$, with probability tending to one, $X_{k,N}(t) \ge N - C_2\log N/s_N$ for all $t$ with $T_{k,N} + C_1\log N/s_N \le t < T_{k+1,N}$: each new type sweeps to near-fixation within time $O(\log N/s_N)$.

**Corollary.** With $\bar X_N(t) = N^{-1}\sum_k k X_{k,N}(t)$ the mean number of mutations, the finite-dimensional distributions of $\big(\bar X_N(t/(N\mu_N s_N))\big)_{t \ge 0}$ converge to those of a rate-one Poisson process.

## Expansion

Beneficial mutations arise in the resident type at total rate $N\mu_N$, and each survives drift and establishes with probability about $s_N$, so successful mutations appear at rate $N\mu_N s_N$; once established, a sweep takes time of order $\log N/s_N$. The condition $\mu_N \ll 1/(N\log N)$ makes $N\mu_N s_N \cdot \log N/s_N \to 0$: the expected number of successful mutations arising during a sweep vanishes, so successive sweeps are separated and the establishment times form a Poisson process. The theorem holds even in parameter ranges where unsuccessful competing mutants with distinct origins occasionally coexist, because such interference only perturbs establishment times on the negligible sweep timescale. The proof couples each type's count with branching processes with immigration from above and below, inductively over successive sweeps.

## Sources

- Nantawat Udomchatpitak and Jason Schweinsberg, "The accumulation of beneficial mutations and convergence to a Poisson process", Stoch. Process. Appl. 183 (2025), 104578, <https://doi.org/10.1016/j.spa.2025.104578>. Numbering follows the arXiv version, arXiv:2407.01999 (2024): standing assumptions on $\mu_N, s_N$, Theorem 1.1 and Corollary 1.2 (Section 1), Propositions 4.17 and 5.5, <https://doi.org/10.48550/arXiv.2407.01999>.
