# Total length of the ancestral learning graph and the number of cultural traits

**Model.** A population of fixed size $N$ evolves in continuous time. Each individual dies at rate $u$ and is replaced by a newborn with no traits; at rate $s$ it learns from a uniformly chosen cultural parent (possibly itself) and adds all of the parent's traits to its own; and at rate $\mu$ it invents a new trait. Tracing backward from a sample of $n$ individuals, the set of lineages from which the sample could have learned forms the *ancestral learning graph* (ALG), the cultural analogue of the ancestral selection graph. Its number of lines $Y(\tau)$ at backward time $\tau$ is the stochastic logistic birth–death chain on $\{0, \dots, N\}$ with $Y(0) = n$, absorbed at $0$, with rates

$$\lambda_y = s\,y\,\frac{N-y}{N} \quad(\text{branching by learning}), \qquad \mu_y = u\,y \quad(\text{loss by death}).$$

Let $L_n = \int_0^\infty Y(\tau)\,d\tau$ be the total length of the genealogy and $C_n$ the number of traits of the sample (in stationarity).

**Proposition (sojourn times).** For a birth–death chain absorbed at $0$ with rates $\lambda_j, \mu_j$, the expected total time spent in state $j \ge \ell$ between the first hitting of $\ell$ and of $\ell - 1$ is $\eta_{\ell j} = \frac{\lambda_\ell\cdots\lambda_{j-1}}{\mu_\ell\cdots\mu_j}$, independent of the starting state; hence the expected sojourn time in $j$ from $i$ is $\zeta_{ij} = \sum_{\ell=1}^{\min\{i,j\}}\eta_{\ell j}$, and for a path integral $\mathcal{I}_i(f) = \int_0^\infty f(Z(t))\,dt$,

$$\mathbb{E}\big[\mathcal{I}_i(f)^m\big] = m!\sum_{j_1,\dots,j_m = 1}^N \zeta_{ij_1}\zeta_{j_1j_2}\cdots\zeta_{j_{m-1}j_m}\,f(j_1)\cdots f(j_m).$$

**Theorem (genealogy length and traits).** For the ALG,

$$\zeta_{nj} = \sum_{\ell=1}^{\min\{n,j\}}\frac{1}{uj}\Big(\frac{s}{Nu}\Big)^{j-\ell}(N-\ell)_{j-\ell},$$

with $(x)_k$ the falling factorial, so $\mathbb{E}[L_n^m] = m!\sum_{j_1,\dots,j_m}\zeta_{nj_1}\zeta_{j_1j_2}\cdots\zeta_{j_{m-1}j_m}\,j_1\cdots j_m$ (in particular $\mathbb{E}L_n = \sum_j j\,\zeta_{nj}$). Since innovations fall as a Poisson process of rate $\mu$ on the lines of the ALG, conditionally on the genealogy $C_n \sim \operatorname{Poi}(\mu L_n)$, so the factorial moments of $C_n$ are $\mathbb{E}[(C_n)_m] = \mu^m\,\mathbb{E}[L_n^m]$.

In the source's forward simulations of the supercritical regime ($s > u$), the full-population genealogy length $L_N$ exhibits a sawtooth reflecting the metastability of the logistic chain near its quasi-stationary level $N(1 - u/s)$ when $s > u$.

## Proof idea

Every learning arrow hitting a line of the backward graph adds the cultural parent as a potential ancestor, and a death removes a line because a newborn has no traits, so the ALG line count jumps $y \to y+1$ at rate $s y (N-y)/N$ and $y \to y-1$ at rate $u y$. The sample's trait set is exactly the set of innovations falling on the ALG, which gives the mixed Poisson law and reduces trait statistics to the path integral $L_n$. The moment formula follows from the strong Markov property: the $m$-th moment of an additive functional is obtained by ordering the $m$ visit times and using expected sojourn times between successive visited states.

## Sources

- J. Y. Wakano, H. Ohtsuki, Y. Kobayashi and E. Baake, "Evolving genealogies in cultural evolution, the descendant process, and the number of cultural traits", Theoretical Population Biology 168 (2026), 1–18, <https://doi.org/10.1016/j.tpb.2025.12.003>. Numbering as in the preprint arXiv:2505.08677v2, <https://arxiv.org/abs/2505.08677v2>: Section 2 (the model and the ALG), Section 3.1 (Eq. (15) and Eqs. (17)–(22)) and Appendices A–B.
