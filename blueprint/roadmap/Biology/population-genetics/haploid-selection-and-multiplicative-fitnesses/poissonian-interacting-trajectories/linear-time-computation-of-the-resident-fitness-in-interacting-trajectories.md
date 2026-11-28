# Linear-time computation of the resident fitness in interacting trajectories

**System.** Given birth times and initial slopes $\beth = ((t_i, a_i))_{1 \le i \le n}$ with $0 \le t_1 < \dots < t_n$ and $a_i > 0$, define continuous piecewise linear trajectories $h_0, \dots, h_n : [0,\infty) \to [0,1]$ (log-sizes of clones on a scale where $1$ means "resident"):

- $h_0(0) = 1$ with slope $0$; each $h_i$, $i \ge 1$, has height $0$ until $t_i$ and then slope $a_i$;
- whenever some trajectory reaches height $1$ from below at time $t$ (a *resident change time*), the slopes of all trajectories with height in $(0,1]$ are reduced by $v^* = \max\{v_i(t-) : h_i(t) = 1\}$;
- a trajectory that reaches $0$ from above stays at $0$ forever.

The *resident type* $\varrho(t)$ is the index attaining $v^*$ at the last resident change time, and the *resident fitness* $f$ jumps by $v^*$ at each resident change time and is constant in between.

**Results.**

1. *(Continued-lines representation.)* Let $\ell_0 \equiv 1$ and, recursively, let $\ell_{k+1}$ be the half-line starting at $(t_{k+1}, \ell^r_k(t_{k+1}) - 1)$ with slope $(\ell^r_k)'(t_{k+1}) + a_{k+1}$, where $\ell^r_k = \max(\ell_0, \dots, \ell_k)$; let $\ell^r$ be the convex upper envelope. For non-degenerate $\beth$, $h_i(s) = \ell_i(s) - \ell^r(s) + 1$ from $t_i$ until this quantity first hits $0$, and $h_i = 0$ otherwise. This identifies the resident change times from the envelope $\ell^r$.
2. *(Complexity.)* Simulating the trajectories directly can require $\Omega(n^2)$ slope updates: there are inputs with $n(n+1)$ slope changes at resident change times. Nevertheless, computing $t \mapsto \varrho(t)$ for any finite, non-degenerate, ordered $\beth$ of size $n$ has algorithmic complexity $\Theta(n)$. If all initial slopes lie in $\{1, \dots, k\}$, all slope functions $t \mapsto v_i(t)$ can be computed in time $O(kn)$.
3. *(Poissonian input.)* Consider the system of Poissonian interacting trajectories $\mathrm{PIT}(\lambda,\gamma)$: the birth times $T_1 < T_2 < \cdots$ are the arrival times of a Poisson process of intensity $\lambda > 0$ (so, with $T_0 = 0$, the gaps $T_i - T_{i-1}$ are i.i.d. exponential with parameter $\lambda$), and the initial slopes $A_1, A_2, \dots$ are i.i.d. strictly positive random variables with common law $\gamma$ on $(0,\infty)$, independent of the birth times. For this input, the expected number $\mathbb E(K_t)$ of slope changes at resident change times up to time $t$ is $O(t)$, and $K_t/t$ converges almost surely to $\mathbb E(K_{E_1})/\mathbb E(E_1) \in (0,\infty)$, for every choice of $\gamma$, where $E_1$ is the first *renewal extinction time* (a time when a new resident is the only clone of positive height) and successive renewal extinction times delimit i.i.d. cycles.

## Expansion

The key observation is that subtracting the resident's slope from everyone is the same as measuring each clone relative to the running maximum. Lifting the trajectories back by the cumulative subtraction turns them into straight half-lines, and the resident is whichever half-line is on top. Lines are added in increasing order of start time, so their convex upper envelope can be maintained incrementally with amortized constant work per line, which is what makes a linear bound possible, while the naive simulation pays for every live clone at every resident change. Biologically, $f$ is the fitness of the currently dominant clone, so the algorithm computes the speed of adaptation under clonal interference in this scaling limit.

## Sources

- Katalin Friedl, Viktória Nemkin and András Tóbiás, "Resident Fitness Computation in Linear Time and Other Algorithmic Aspects of Interacting Trajectories", *Random Structures & Algorithms* 69 (2026), e70087, <https://doi.org/10.1002/rsa.70087>. Numbering as in the preprint arXiv:2502.11561v4, <https://arxiv.org/abs/2502.11561v4>: Definitions 2.1–2.2, Lemma 2.7, Proposition 3.1, Theorem 3.3 (linear complexity), Corollary 3.4, Proposition 3.5, Corollary 3.7.
