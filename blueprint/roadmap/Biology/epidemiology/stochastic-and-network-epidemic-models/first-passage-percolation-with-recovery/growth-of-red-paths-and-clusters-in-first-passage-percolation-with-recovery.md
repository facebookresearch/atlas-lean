# Growth of infected paths and clusters in first passage percolation with recovery

**Model.** On a connected graph $G=(V,E)$ with reference vertex $o$, put i.i.d. Exponential$(1)$ passage times $T_e$ on the edges and i.i.d. Exponential$(\gamma)$ recovery clocks $C_v$, $\gamma>0$, on the vertices. Vertex $v$ is *reached* at its first-passage time

$$\tau_v = \inf_{\pi: o \to v} \sum_{e \in \pi} T_e,$$

is *red* (infected) during $[\tau_v, \tau_v + C_v)$ and *black* (recovered) afterwards, never turning red again. Equivalently: a red particle starts at $o$, every reached seed turns red and spreads first passage percolation of rate $1$, and red vertices turn black at rate $\gamma$; recovery changes colours but does not slow the spread. Let $A_t = \{v : \tau_v \le t\}$, let $H_t$ be the number of vertices of the longest (oriented) red path at time $t$, and $M_t$ the size of the largest red cluster.

**Theorem (semi-line).** If $G = \mathbb{N}$, then for every $\gamma > 0$, almost surely

$$\limsup_{t\to\infty} \frac{H_t \log\log t}{\log t} = 1, \qquad \liminf_{t\to\infty} H_t = 0 .$$

**Theorem (supercritical Galton–Watson trees).** If $G$ is a Galton–Watson tree with offspring mean $m \in (1,\infty)$, then for every $\gamma > 0$, almost surely on the event that $G$ is infinite,

$$\liminf_{t\to\infty}\frac{H_t\log t}{t} \ge m-1, \qquad \liminf_{t\to\infty}\frac{M_t\log\log t}{t} \ge m-1,$$

and $\liminf_t H_t \log\log(\#A_t)/\log(\#A_t) \ge 1$. Moreover, almost surely $M_t e^{-(m-1+\delta)t} \to 0$ for every $\delta > 0$, and $\limsup_t H_t/t \le \bar c$ for a constant $\bar c > 1$.

**Proposition (bounded degree).** If $G$ has bounded degree, then for every $\varepsilon > 0$ there is $\gamma_c > 0$ such that for all $\gamma > \gamma_c$, almost surely $\limsup_t M_t/t \le \varepsilon$.

So although the reached set always grows, on the line the infected region is only of logarithmic length infinitely often and empty infinitely often, while on trees with exponential growth the infected set itself grows at least linearly.

## Expansion

On $\mathbb{N}$, vertex $n$ is reached at time $\tau_n = \sum_{i<n} T_{(i,i+1)} \approx n$, and a red path ending near the front is a run of consecutive vertices whose recovery clocks outlast the remaining passage times; such runs have geometric-type tails, so the record run length among the $n \approx t$ reached vertices is of order $\log n/\log\log n$, while infinitely often the most recently reached vertex recovers before the next is reached, leaving no red vertex. On a supercritical Galton–Watson tree, the reached set grows like $e^{(m-1)t}$ and there are exponentially many rays; a second-moment argument along the boundary finds rays whose last $\approx t/\log t$ vertices were all reached within a time window shorter than their recovery clocks. The upper bounds compare $M_t$ with the size of the reached set and $H_t$ with the height of first passage percolation.

## Sources

- Elisabetta Candellero and Tom Garcia-Sanchez, "First passage percolation with recovery", Stochastic Processes and their Applications 179 (2025), 104512, <https://doi.org/10.1016/j.spa.2024.104512>; numbering as in arXiv:2402.03930: Theorems 1.1 and 1.2, Corollary 1.3 and Proposition 1.4.
