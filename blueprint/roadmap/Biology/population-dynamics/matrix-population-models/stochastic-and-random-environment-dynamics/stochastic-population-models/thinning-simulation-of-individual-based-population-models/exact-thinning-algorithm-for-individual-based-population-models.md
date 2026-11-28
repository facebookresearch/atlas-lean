# Exact thinning algorithm for individual-based population models

**Model.** A population at time $t$ is the point measure $Z_t = \sum_{k=1}^{N_t} \delta_{I_k}$, where each individual $I = (\tau, x)$ carries its birth date $\tau$ (so its age at time $t$ is $t - \tau$) and characteristics $x$. The population changes through events $e$ of several types (birth, death, entry, exit, change of characteristics). Each individual experiences events of type $e$ at an intensity that is either
- *Poisson:* a deterministic population-level rate $\mu^e(t)$;
- *without interaction:* $\lambda^e(t, I)$, depending only on the individual and time;
- *with interaction:* $\lambda^e(t, I, Z_t) = \sum_{j=1}^{N_t} W^e(t, I, I_j)$, a sum of pairwise interaction kernels.

The population process is the solution of a stochastic differential equation driven by Poisson random measures, with global event intensity $\Lambda^e_t(Z_t) = \sum_k \lambda^e(t, I_k, Z_t)$.

**Proposition (thinning).** Let $\bar Q$ be a Poisson random measure on $[0,T]\times\mathbb R_+$ with Lebesgue intensity and atoms $(\bar T_\ell, \bar\Theta_\ell)$, and let $\Lambda$ be a non-negative function with $\Lambda \le \bar\Lambda$. Then

$$N^\Lambda_t = \sum_{\ell \ge 1} \mathbf 1_{\{\bar T_\ell \le t\}}\, \mathbf 1_{\{\bar\Theta_\ell \le \Lambda(\bar T_\ell)\}}$$

is an inhomogeneous Poisson process with intensity $\Lambda$. Equivalently, candidate event times are generated at the dominating rate $\bar\Lambda$ and each is accepted with probability $\Lambda(\bar T_\ell)/\bar\Lambda$.

**Bounds used for simulation.** If $\mu^e \le \bar\mu^e$, $\lambda^e(t, I) \le \bar\lambda^e$ and $W^e \le \bar W^e$ on $[0,T]$, then $\Lambda^e_t(Z_t)$ is dominated by $\bar\mu^e$, $\bar\lambda^e N_t$ or $\bar W^e N_t^2$ respectively, so between events the candidate rate is constant and the whole population path is simulated exactly, without time discretization: draw a candidate time, draw the event type and the individual (and, for interactions, a uniformly chosen partner $J$), and accept with probability $\lambda^e(t,I)/\bar\lambda^e$ or $W^e(t,I,J)/\bar W^e$.

**Non-explosion.** If for each birth or entry type $e$ with non-Poisson intensity there is $f^e : \mathbb N \to (0,\infty)$ with $\sum_{n\ge1} 1/(n f^e(n)) = \infty$ and $\lambda^e_t(I, Z) \le f^e(n)$ for every population of size $n$, then the jump times $T_n$ of the population process satisfy $T_n \to \infty$ almost surely.

## Proof sketch

Thinning (Lewis–Shedler) follows from the mapping and restriction theorems for Poisson random measures: restricting $\bar Q$ to the region under the graph of $\Lambda$ gives a Poisson measure whose time projection has intensity $\Lambda(t)\,dt$. Applied with the population-dependent bound $\bar\lambda^e N_t$ (piecewise constant between events), it yields an exact simulation algorithm whose cost per accepted event is governed by the ratio $\bar\lambda^e/\lambda^e$. For interactions, randomizing the partner replaces the $O(N_t)$ evaluation of $\sum_j W^e(t, I, I_j)$ by a single kernel evaluation. Non-explosion follows by comparing the total population with a pure birth process of rates $n f(n)$, which is non-explosive exactly when $\sum 1/(n f(n)) = \infty$.

## Sources

- Daphné Giorgi, Sarah Kaakai and Vincent Lemaire, "Efficient simulation of individual-based population models", *Computo* (2024), <https://doi.org/10.57750/sfxn-1t05>. Preprint version: arXiv:2303.06183 (2023), intensity assumptions, non-explosion lemma and the thinning proposition, <https://doi.org/10.48550/arXiv.2303.06183>.
