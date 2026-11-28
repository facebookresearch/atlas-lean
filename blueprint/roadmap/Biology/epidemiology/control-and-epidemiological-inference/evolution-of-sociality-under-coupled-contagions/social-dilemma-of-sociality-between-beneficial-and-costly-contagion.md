# Social dilemma of sociality between a beneficial and a costly contagion

Individuals meet at social contact rate $\sigma$. A good contagion ($g$) and a bad contagion ($b$) each follow SIS dynamics with per-contact transmission probabilities $p_g, p_b$ and recovery rates $\gamma_g, \gamma_b$, so

$$R^{(g)} = \frac{\sigma p_g}{\gamma_g}, \qquad R^{(b)} = c\,R^{(g)}, \qquad c = \frac{p_b \gamma_g}{p_g \gamma_b},$$

and $c$ is the relative transmissibility of the bad contagion. In a monomorphic population the globally stable prevalences are $\hat I^{(g)} = (1 - 1/R^{(g)})_+$ and $\hat I^{(b)} = (1 - 1/(cR^{(g)}))_+$. Fitness is the Cobb–Douglas utility $U = (\hat I^{(g)})^{\alpha}(\hat S^{(b)})^{1-\alpha}$ with weight $\alpha \in (0,1)$ on the good contagion and $\hat S^{(b)} = 1 - \hat I^{(b)}$.

**Social optimum.** The monomorphic utility is maximized at $R^{(g)}_{\mathrm{opt}} = \max\!\left(\tfrac1c,\ \tfrac{1}{1-\alpha}\right)$.

**Dimorphic competition.** With a mutant strategy at frequency $f$ and contacts mixing in proportion to contact rates, the combined good contagion has

$$R^{(g)}_{\mathrm{net}} = \frac{f (R^{(g)}_m)^2 + (1-f)(R^{(g)}_r)^2}{f R^{(g)}_m + (1-f) R^{(g)}_r},$$

with a globally stable disease-free state if $R^{(g)}_{\mathrm{net}} < 1$ and a unique globally attracting endemic state if $R^{(g)}_{\mathrm{net}} > 1$; likewise for the bad contagion with $c R^{(g)}_{\mathrm{net}}$. Strategy frequencies follow the replicator equation $\dot f = f(1-f)[U_m(f) - U_r(f)]$.

**Proposition.** If $R^{(g)}_r, R^{(g)}_m \ge 1$, $R^{(g)}_r \ne R^{(g)}_m$ and one of them exceeds $1$, then for every $c > 0$ the log-utility difference $\log U_m(f) - \log U_r(f)$ is strictly decreasing in $f$. Hence exactly one of the following holds: the mutant takes over (it is fitter at both $f = 0$ and $f = 1$), the resident takes over (it is fitter at both ends), or the mutant is fitter when rare and less fit when common, and the two strategies coexist at a unique globally stable interior frequency. Bistability cannot occur.

**Evolutionarily stable sociality.** Under adaptive dynamics the unique singular strategy gives the ESS

$$R^{(g)}_{\mathrm{ESS}} = \max\!\left(1,\ \frac{1}{c} + \frac{\alpha}{1-\alpha}\right),$$

and $R^{(g)}_{\mathrm{ESS}} > R^{(g)}_{\mathrm{opt}}$ when $c < 1$, $R^{(g)}_{\mathrm{ESS}} = R^{(g)}_{\mathrm{opt}}$ when $c = 1$, and $R^{(g)}_{\mathrm{ESS}} < R^{(g)}_{\mathrm{opt}}$ when $c > 1$. The ordering holds for a broader class of utilities with a unique social optimum.

## Expansion

For a rare mutant the resident sits at the monomorphic equilibrium and the mutant's prevalences are explicit, for example $\hat S^{(b)}_m = R^{(g)}_r / [R^{(g)}_m (cR^{(g)}_r - 1) + R^{(g)}_r]$ when $R^{(g)}_r > 1/c$. Differentiating the mutant log-utility at $R^{(g)}_m = R^{(g)}_r$ gives a local selection gradient that is positive below $1/c$ and decreasing above it, so it has a single zero, which is the ESS when it is at least $1$. The dilemma arises because a mutant's contact rate changes its own exposure but its effect on population prevalence is diluted. When the good contagion spreads more easily ($c < 1$), selection overshoots the optimum and sustains the bad contagion even where the optimum would eliminate it. When the bad contagion spreads more easily ($c > 1$), selection undershoots. The two coincide only in the structurally unstable case $c = 1$.

## Sources

- D. B. Cooney, D. H. Morris, S. A. Levin, D. I. Rubenstein, P. Romanczuk, "Social dilemmas of sociality due to beneficial and costly contagion", PLoS Computational Biology (2022), Eqs. (2)–(12), (8), (10), (16), (27), Proposition 1 and Table 1, <https://doi.org/10.1371/journal.pcbi.1010670>, PMCID PMC9721494.
