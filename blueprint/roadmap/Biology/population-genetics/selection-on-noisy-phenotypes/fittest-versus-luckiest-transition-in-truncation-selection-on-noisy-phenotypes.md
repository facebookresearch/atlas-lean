# Fittest-versus-luckiest transition in truncation selection on noisy phenotypes

**Model.** An asexual population has $N$ juveniles per generation, of which the $K = N^{\gamma}$ with the largest *phenotypes* survive ($\gamma \in (0,1)$ measures reproductive skew), and each survivor has $N^{1-\gamma}$ children. A child of a parent with genotype $g$ has genotype $g + X$ and phenotype $g + X + Y$, with independent Laplace noises: $X$ has density $\propto e^{-|x|}$ and $Y$ has density $\propto e^{-\mu|y|}$, so $\mu > 0$ is the ratio of genotypic to phenotypic noise scale. Only genotypes are inherited.

**Log-scaled dynamics.** Describe the population by a profile $g_n$, meaning about $N^{g_n(y)}dy$ individuals have genotype in $[y\log N, (y+dy)\log N]$, and let $\pi(h) = h$ for $h \ge 0$ and $-\infty$ otherwise. As $N \to \infty$ the generation map becomes

$$p_{n+1}(z) = \pi\Big(1 - \gamma + \sup_y\big(g_n(y) - \min(1,\mu)(z - y)_+\big)\Big),\qquad s_{n+1} = \sup\{z : p_{n+1}(z) \ge \gamma\},$$

$$g_{n+1}(x) = \pi\Big(1 - \gamma + \sup_y\big(g_n(y) - |x - y|\big) - \mu\,(s_{n+1} - x)_+\Big),$$

where $p_{n+1}$ is the log-profile of children's phenotypes and $s_{n+1}$ the log-scaled selection threshold. Concavity of $g_0$ propagates to all $g_n$ and $p_n$.

**Theorem.** Let $\gamma \in (0,1)$, $\mu > 0$, $\mu \ne 1$, and $k = \lfloor 1/\mu\rfloor$. The dynamics has a traveling wave $g_n(x) = g(x - nv)$, concave with compact support and unique up to translation, with speed

$$v(\gamma,\mu) = \begin{cases} \dfrac{2\gamma}{k\big(2 - (k+1)\mu\big)}, & \gamma < \gamma_c(\mu),\\[2mm] 1 - \gamma, & \gamma > \gamma_c(\mu),\end{cases}\qquad \gamma_c(\mu) = \frac{k}{k+1}\Big(1 - \frac{\mu}{2 - k\mu}\Big).$$

So $\gamma \mapsto v$ increases on $(0, \gamma_c]$ and decreases on $[\gamma_c, 1)$: selection stronger than $\gamma_c$ (smaller $\gamma$) slows adaptation. For $\gamma < \gamma_c$ the wave is fully pulled, with piecewise-linear profile of slopes $g'(x) = j\mu - 1$ on $(-jv, -(j-1)v)$, and survivors' genotypes are strictly fewer than children's at every genotype (selection of the luckiest: the leading edge is made of lucky phenotypic draws). For $\gamma > \gamma_c$ the wave is semipulled, the survivors' and children's genotype profiles coincide near the leading edge (selection of the fittest), and ancestral lineages settle at a fixed distance behind the front.

## Depends on

## Expansion

By Laplace's principle, the number of children above phenotype $z\log N$ is $N^{p_{n+1}(z)}$, and truncation keeps those above the level where this count is $N^\gamma$; survivors with genotype near $x\log N$ pay a factor $N^{-\mu(s-x)_+}$ for the phenotypic noise needed to cross the threshold. A traveling wave must be a fixed point of this max-plus map modulo translation. If the threshold $s$ lies ahead of the genotypic front, survivors are individuals whose phenotypic luck carried them over $s$, the wave is pushed by its tip and its slopes step through $j\mu - 1$, giving the first speed formula; if the threshold lies within the genotypic support, the fittest genotypes survive outright and the front moves at the rate $1 - \gamma$ at which fertility can push genotypes forward. Equating the two regimes gives $\gamma_c$.

## Sources

- B. Mallein, F. Paparella, E. Schertzer and Z. Talyigás, "Selection of the fittest or selection of the luckiest: the emergence of Goodhart's law in evolution", arXiv:2503.21849 (2025), Section 2, Theorems 7.1–7.3, Propositions 8.2, 9.5 and Theorem 9.1, <https://doi.org/10.48550/arXiv.2503.21849>.
