# Lower bound on the critical infection probability of range-R SIR epidemics in dimensions four to six

**Model.** On $\mathbb Z^d$ join $x \ne y$ whenever $\|x - y\|_\infty \le R$, so each site has $V(R) = (2R+1)^d - 1$ neighbours. In range-$R$ bond percolation each edge is open independently with probability $p$; $p_c(R)$ is the critical probability for an infinite open cluster. Equivalently, consider the discrete-time SIR epidemic started from one infective at the origin: an infective at generation $n$ tries to infect each susceptible neighbour independently with probability $p$, then is removed forever. The set of ever-infected sites is the open cluster of the origin, so $p_c(R)$ is the critical infection probability for the epidemic to survive. A mean-field branching comparison gives $p_c(R)V(R) \ge 1$.

**Theorem.** Let $4 \le d \le 6$ and $b_4 = 9/(2\pi^2)$; for $d = 5,6$ let

$$b_d = 2^{-d}\sum_{k=1}^\infty \Big\lfloor \frac{k+2}{2}\Big\rfloor\, P\big(U_k \in [-1,1]^d\big),$$

where $U_k$ is the sum of $k$ independent uniform random vectors on $[-1,1]^d$. For every $\theta < b_d$ there is $c(\theta) > 0$ such that for all integers $R > c(\theta)$,

$$p_c(R)V(R) - 1 \ge \begin{cases} \theta\,\dfrac{\log R}{R^4}, & d = 4,\\[6pt] \dfrac{\theta}{R^d}, & d = 5, 6.\end{cases}$$

In particular $\liminf_{R\to\infty} [p_c(R)V(R) - 1]R^4/\log R \ge b_4$ in $d = 4$ and $\liminf_{R\to\infty}[p_c(R)V(R) - 1]R^d \ge b_d$ in $d = 5, 6$, matching the conjectured order of the correction to the mean-field value.

## Proof sketch

The proof shows that the SIR epidemic dies out when $p(R)V(R) = 1 + \theta/N_R$ with $N_R$ of order $R^4/\log R$ ($d=4$) or $R^d$ ($d = 5,6$). The epidemic is dominated by a branching random walk, but that walk is supercritical at this $p$, so instead one couples the epidemic inside a *self-avoiding* branching random walk in which births onto previously visited sites are suppressed. The suppressed births come from collisions of a lineage with its own past range; their expected number over about $N_R$ generations is computed through the local time of the uniform random walk $U_k$ near the origin, which produces the constant $b_d$. Showing that some generation $k_0 \le N_R + 1$ has expected size below $1$ then forces extinction. In $d > 6$ (van der Hofstad–Sakai) and $d \le 3$ the analogous asymptotics are known, so this fills in the critical dimensions $4 \le d \le 6$.

## Sources

- Jieliang Hong, "A lower bound for pc in range-R bond percolation in four, five and six dimensions", *Stochastic Processes and their Applications* 185 (2025), 104637, <https://doi.org/10.1016/j.spa.2025.104637>. Preprint version: arXiv:2307.01466 (2023), main theorem, SIR and self-avoiding branching random walk coupling lemmas and the extinction proposition, <https://doi.org/10.48550/arXiv.2307.01466>.
