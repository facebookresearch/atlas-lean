# Absorption and fixation times of proliferation processes on graphs

**Setting.** A population of $N$ individuals occupies the vertices of a connected undirected graph $G=(V,E)$; mutants have relative fitness $r>0$. At each step a vertex $v$ is chosen with probability proportional to fitness ($r$ for a mutant, $1$ for a resident). In the **Moran process** a uniformly chosen neighbour of $v$ receives a copy of $v$'s type. In a **proliferation process** with parameter $p\in(0,1]$, residents still replace one random neighbour, but a mutant at $v$ proliferates: under *Bernoulli proliferation* all $d(v)$ neighbours become mutants with probability $p$ (and nothing happens otherwise); under *binomial proliferation* each neighbour independently becomes a mutant with probability $p$. Let $\Phi_1(r)$ be the mean fixation probability of a single mutant placed at a uniform vertex, $\tau_1$ the mean absorption time (until fixation or extinction) and $T_1$ the mean fixation time (conditioned on fixation), with superscripts $M$, $B$, $b$ for Moran, Bernoulli and binomial dynamics. The absorption and fixation time ratios are

$$\rho^\beta(r,p)=\frac{\tau_1^M(r)}{\tau_1^\beta(r,p)},\qquad P^\beta(r,p)=\frac{T_1^M(r)}{T_1^\beta(r,p)},\qquad \beta\in\{B,b\}.$$

**Theorem 2.1 (critical proliferation).** For every graph and fitness $r>0$ there are unique critical values $p_c^B(r)$, $p_c^b(r)$ with $\Phi_1^B(r,p_c^B)=\Phi_1^M(r)$ and $\Phi_1^b(r,p_c^b)=\Phi_1^M(r)$; proliferation is advantageous for fixation above them and disadvantageous below.

**Theorems 2.2-2.4 (monotonicity).** For every vertex $v$, the Moran fixation time $T^M_{\{v\}}(r)$ is decreasing in $r$ for $r$ large enough. For proliferation, $T^\beta_{\{v\}}(r,p')\ge T^\beta_{\{v\}}(r,p)$ whenever $0<p'\le p$. For every $r$ there is a threshold $p_t^\beta(r)$ with $P^\beta(r,p)\le1$ for $p\le p_t^\beta$ and $P^\beta(r,p)\ge1$ for $p\ge p_t^\beta$.

**Propositions 3.1-3.5 (critical Bernoulli proliferation, $r\to\infty$).** With $H_{N-1}=\sum_{j=1}^{N-1}1/j$:
- complete graph $K_N$: $\lim_{r\to\infty}\rho^B(r,p_c)=\lim_{r\to\infty}P^B(r,p_c)=(N-1)H_{N-1}$;
- cycle $C_N$: $\lim_{r\to\infty}\rho^B(r,p_c)=\lim_{r\to\infty}P^B(r,p_c)=\dfrac{2N(N-1)}{(N+1)(N-2)}$;
- star with $N$ vertices: $\lim_{r\to\infty}\rho^B(r,p_c)=\dfrac{N}{3N-2}\,(N-1)\sum_{i=1}^{N-1}H_i$.

## Expansion

As $r\to\infty$ fixation becomes certain for every dynamics and absorption and fixation times coincide (Proposition 2.1). On the complete graph a Moran mutant lineage then grows by one at each mutant step, so the time to fill the graph is a coupon-collector sum of order $(N-1)H_{N-1}$ generations, whereas a single successful Bernoulli proliferation event fills all $N-1$ neighbours at once; this gives the ratio $(N-1)H_{N-1}$. On the cycle, proliferation converts both neighbours of the boundary mutant, roughly doubling the front speed, which yields a ratio close to $2$. On the star, the time is governed by alternation between the centre and the leaves. The monotonicity in $p$ follows from a coupling of proliferation processes with different intensities on a common graphical construction (Section 5).

## Sources

- F. Alcalde Cuesta, G. Guerberoff, Á. Lozano Rojo, "Absorption and fixation times for evolutionary processes on graphs", *Royal Society Open Science* 13(11) (2026), 260131, Theorems 2.1-2.4, Proposition 2.1, Propositions 3.1-3.5, <https://doi.org/10.1098/rsos.260131> (preprint arXiv:2601.09737).
