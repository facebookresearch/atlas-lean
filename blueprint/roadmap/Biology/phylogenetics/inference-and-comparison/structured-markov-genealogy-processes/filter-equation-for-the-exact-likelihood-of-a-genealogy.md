# Filter equation for the exact likelihood of a genealogy

**Setting.** A Markov population process $X_t$ on a state space $\mathcal X$ jumps from $x$ to $x'$ through events of mark $u$ at rate $\alpha_u(t,x,x')$, starting from the law $p_0$. Individuals live in demes; $n(x)$ is the deme occupancy vector, and an event of mark $u$ has production $r^u$, the deme vector of lineages emerging from it (surviving parents included, dead lineages excluded). The genealogy process records the full ancestry of all individuals; sampling events mark tips. The pruned genealogy $\mathcal P$ keeps only the ancestry of sampled lineages; at time $t$ it has lineage-count vector $\ell(Y_t)$, and $s(Y_t)$ counts lineages emerging from the genealogy's nodes at $t$. A compatibility indicator $Q_u(y',y)$ says whether an event of mark $u$ can carry the genealogy from state $y'$ just before $t$ to $y$ just after. With the binomial ratio

$$\begin{pmatrix}n&\ell\\ r&s\end{pmatrix}=\frac{\prod_i\binom{n_i-\ell_i}{r_i-s_i}}{\prod_i\binom{n_i}{r_i}}\ \ (\text{if }n_i\ge\ell_i,r_i\ge s_i\ge0;\ 0\text{ otherwise}),$$

define $\phi_u(x,y',y)=\begin{pmatrix}n(x)&\ell(y)\\ r^u&s(y)\end{pmatrix}Q_u(y',y)$.

**Theorem 1 (conditional likelihood).** Given the full history $\mathcal H$ of the population process up to $T$,

$$\mathbb P(\mathcal P_T=\mathcal P\mid\mathcal H_T=\mathcal H)=\mathbf 1\{\text{event times of }\mathcal H\supseteq\text{node times of }\mathcal P\}\prod_{t\in\text{events of }\mathcal H}\phi_{U_t}(X_t,Y_{t-},Y_t).$$

**Theorem 2 (filter equation).** Let $w(t,x)$ be càdlàg with $w(0,x)=p_0(x)$ and

$$\partial_tw(t,x)=\sum_u\!\int w(t,x')\,\alpha_u(t,x',x)\,\phi_u(x,Y_{t-},Y_t)\,dx'-\sum_u\!\int w(t,x)\,\alpha_u(t,x,x')\,dx'$$

between node times of $\mathcal P$, and at a node time $t$

$$w(t,x)=\sum_u\!\int w(t-,x')\,\alpha_u(t,x',x)\,\phi_u(x,Y_{t-},Y_t)\,dx'.$$

Then the likelihood of the pruned genealogy is $\mathcal L(\mathcal P)=\int w(T,x)\,dx$. An adjoint backward equation for $F(s,x)$ with $F(T,x)=1$ gives the same likelihood. For obscured genealogies (deme labels of lineages unobserved) an analogous filter on $(x,y)$ with importance kernels holds.

**Special cases.** The constant-size Moran model gives the Kingman coalescent likelihood, and the linear birth–death–sampling process gives the closed-form birth–death likelihood; general nonlinear compartmental models (SIR, SEIR, multi-host) fall in the same framework.

## Depends on

- [Coalescents](../../../coalescent-theory/coalescents/README.md)

## Expansion

Given the population history, each event picks which of the existing lineages are its offspring uniformly among those of the right demes; the probability that it is compatible with the observed genealogy, i.e. that exactly the genealogy's emerging lineages are among the $r^u$ produced and none of the other $\ell-s$ lineages are, is the hypergeometric-type binomial ratio. Theorem 1 multiplies these factors over events, and Theorem 2 integrates out the history: $w(t,\cdot)$ is the unnormalized density of $X_t$ jointly with the genealogy observed up to $t$, a Kolmogorov forward equation reweighted by $\phi_u$. Non-locality of genealogies in time is resolved because the factors depend only on the current lineage counts. For nonlinear models the filter equation is solved numerically, for example by particle (sequential Monte Carlo) methods.

## Sources

- A. A. King, Q. Lin, E. L. Ionides, "Exact phylodynamic likelihood via structured Markov genealogy processes", *Theoretical Population Biology* 171 (2026), 79–105, Section 3 (genealogy process, binomial ratio, production, lineage-count and saturation functions), Theorems 1 and 2, Corollary 3, Theorems 4 and 5, <https://doi.org/10.1016/j.tpb.2026.07.002> (preprint arXiv:2405.17032).
