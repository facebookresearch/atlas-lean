# Finite-depth genealogical reinforcement in branching

**Model.** Generations are discrete and each individual $v$ has $\xi(v) \in \{0,1,2\}$ offspring. For individuals $u, v$ with most recent common ancestor $\mathrm{MRCA}(u,v)$, the genealogical distance is $d(u,v) = k(u, \mathrm{MRCA}) + k(v, \mathrm{MRCA})$, the sum of generational distances to the common ancestor. For a truncation depth $D$ and decay $\theta \ge 0$, the kin functional of a living individual $v$ in generation $n$ is

$$G(v, \mathcal T_n) = \sum_{u \in \mathcal L_n,\ u \ne v,\ d(u,v) \le 2D} e^{-\theta d(u,v)},$$

summing over living relatives $\mathcal L_n$ within distance $2D$, and

$$\xi(v) \sim \mathrm{Binomial}(2, p(v)), \qquad p(v) = \frac{1}{1 + \exp\big(-\beta_0 - \beta_1 G(v, \mathcal T_n)\big)},$$

with baseline $\beta_0$ and reinforcement strength $\beta_1 \ge 0$. Equivalently the log-odds are $\eta_v = \beta_0 + \beta_1\sum_{d=1}^{2D} c_v(d)e^{-\theta d}$, where $c_v(d)$ counts living relatives at distance $d$. Setting $\beta_1 = 0$ recovers an independent Galton-Watson process; with $\beta_0 < 0$ only reinforcement by large families can rescue the population.

**Theorem 1 (identifiability).** Let $D \ge 2$ and suppose the local subtrees and subsequent branching events of a sample of individuals are observed. Then $(\beta_0, \beta_1, \theta)$ are globally structurally identifiable from the binomial likelihood $\mathcal L(\beta_0, \beta_1, \theta) = \prod_v \binom{2}{\xi(v)}p(v)^{\xi(v)}(1 - p(v))^{2 - \xi(v)}$ if either

- (a) one sampled individual has no relatives in range ($c_v = 0$) and two others have linearly independent count vectors involving at least two distinct nonzero distances; or
- (b) three sampled individuals have linearly independent count vectors and at least three distinct nonzero distances occur in the sample.

For $D \le 1$ the parameters are not identifiable: with siblings only, $\beta_1$ and $\theta$ enter only through $\beta_1 e^{-\theta}$.

**Theorem 2 (tree-valued representation).** A branching process whose offspring law depends on genealogy up to depth $2D$ is a multitype branching process whose types are the rooted subtrees of depth at most $D$ with at most two children per vertex. The number of types satisfies $\rho_D = (\rho_{D-1} + 1)(\rho_{D-1} + 2)/2$ (so $\rho_1 = 3$, $\rho_2 = 10$), and growth is governed by the mean matrix $\mathbf M = (m_{ij})$, $m_{ij}$ the expected number of type-$j$ subtrees produced by a type-$i$ subtree in one generation.

**Testing independence.** For $H_0 : \beta_1 = 0$ against $\beta_1 > 0$, the likelihood ratio statistic does not follow Wilks' $\chi^2$ law or Chernoff's $\tfrac12\chi^2_0 + \tfrac12\chi^2_1$ mixture, because $\beta_1$ lies on the boundary and $\theta$ is unidentified under the null; its null distribution is calibrated by simulation and becomes heavier-tailed as $D$ grows.

## Expansion

In case (a) the isolated individual pins $\eta_v = \beta_0$, and two independent kin profiles with two distinct distances give two equations in $\beta_1 e^{-d_1\theta}$, $\beta_1 e^{-d_2\theta}$, from which $\theta$ is recovered because $\theta \mapsto e^{-\theta d}$ is strictly monotone; case (b) solves for $(\beta_0, \beta_1)$ at fixed $\theta$ and uses three distances to single out $\theta$. The Fisher information is then non-singular, giving local identifiability, and monotonicity in $\theta > 0$ upgrades it to a unique maximizer of the expected likelihood; the finite-sample log-likelihood need not be concave, so maximization uses a global search. For Theorem 2, the offspring law of every individual is a function of the depth-$D$ subtree around it, so the subtree is itself the reproducing unit and the type space is finite; the recurrence counts a root with no children, one child subtree, or an unordered pair of child subtrees of depth $D-1$, and the dominant eigenvalue of $\mathbf M$ separates sub- and supercritical regimes.

## Sources

- A. Kochocki, "Genealogical Reinforcement in Branching Processes" (2026), Section 2 (model), Section 3 (likelihood), Section 4 (Theorem 1), Remark 2 on concavity, Section 5 (likelihood ratio test and empirical null), Section 6 (Theorem 2, type-count recurrence, mean matrix and Example 1), <https://doi.org/10.48550/arXiv.2611.08548>.
