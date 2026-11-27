# Reproduction along a uniform ancestral lineage is a mixed Poisson process

**Setting.** Consider a continuous-time Bienaymé-Galton-Watson process $(N_t)_{t\ge 0}$ with $N_0 = 1$: each cell independently, at rate $r > 0$, is replaced by $k \ge 0$ offspring with probability $p_k$. Let $f(s) = \sum_k p_k s^k$ be the offspring generating function and $F_t(s) = \mathbb E[s^{N_t}]$, which solves $\partial_t F_t(s) = r\bigl(f(F_t(s)) - F_t(s)\bigr)$ with $F_0(s) = s$; write $F_t'(s) = \partial_s F_t(s)$. No criticality assumption is made. On the event $\{N_T \ge 1\}$, sample one cell uniformly from those alive at time $T$ and follow its ancestral lineage back to time $0$.

**Theorem.** Conditionally on $\{N_T \ge 1\}$, the probability that the lineage carries exactly $j$ reproduction events, of sizes $\ell_1, \dots, \ell_j$, in the time intervals $[t_i, t_i + dt_i)$, is

$$\frac{e^{-rT}}{1 - F_T(0)} \int_0^1 \prod_{i=1}^j r \ell_i p_{\ell_i}\, F_{T-t_i}(s)^{\ell_i - 1}\, dt_i \; ds.$$

Equivalently, let $S$ be a random variable on $[0,1]$ with density $F_T'(s)/(1 - F_T(0))$. Given $S$, reproduction events of each size $\ell \ge 1$ occur along the lineage as independent time-inhomogeneous Poisson processes with intensities

$$r_\ell(S, t) = r\, \ell\, p_\ell\, F_{T-t}(S)^{\ell - 1}, \qquad 0 \le t \le T,$$

and no size-$0$ event ever occurs.

**Consequences.** The number $E_T$ of reproduction events on the lineage satisfies

$$\mathbb P(E_T = j \mid N_T \ge 1) = \frac{e^{-rT}}{\mathbb P(N_T \ge 1)} \int_0^1 \frac{\bigl(rT + \log F_T'(s)\bigr)^j}{j!}\, ds,$$

and the instantaneous reproduction rate on the lineage at time $t < T$ is

$$R_T(t) = \frac{r}{1 - F_T(0)} \int_{F_{T-t}(0)}^1 F_t'(s)\, f'(s)\, ds.$$

For a supercritical process $R_T(t)$ increases in $t$. For the Yule process ($p_2 = 1$, $r = 1$), $R(t) = 2\bigl(1 - (t+1)e^{-t}\bigr)/(1 - e^{-t})^2$, rising from $1$ at $t = 0$ to $2$; for the heavy-tailed law $p_k = 1/(k(k-1))$, $k \ge 2$, with $r = 1$, $R(t) = e^t$. Large-population heuristics ($k$-fold rate $r k p_k$ of size-$k$ events) are thus only the long-time limit of a time-varying bias.

## Proof sketch

The proof uses a spine construction: pick a lineage $W_T$ by choosing uniformly among the children at each reproduction, so that its events are a homogeneous Poisson process of rate $r$ with sizes drawn from $(p_k)$, and reweight by $\prod_{v \prec W_T} L_v / N_T$ to make it a uniform sample (a many-to-one identity). The factor $1/N_T$ is handled with $1/n = \int_0^1 s^{n-1} ds$ and the independence of the subtrees hanging off the spine, which produces $\prod F_{T - t_i}(s)^{\ell_i - 1}$. Summing over sizes, the total intensity integrates to $r\int_0^T f'(F_{T-t}(s))\,dt = rT + \log F_T'(s)$, which normalizes the mixture and gives the law of $E_T$. The rate $R_T(t)$ follows by marginalizing one event and using the semigroup property $F_T = F_t \circ F_{T-t}$.

## Sources

- David Cheek and Samuel G. G. Johnston, "Ancestral reproductive bias in branching processes", *Journal of Mathematical Biology* 86 (2023), 70, <https://doi.org/10.1007/s00285-023-01907-7>. Preprint version: arXiv:2205.13875 (2022), Theorems 2.1 and 2.2, Lemmas 2.3-2.5, Proposition 3.1, Proposition 4.1 and Section 4.1, <https://doi.org/10.48550/arXiv.2205.13875>.
