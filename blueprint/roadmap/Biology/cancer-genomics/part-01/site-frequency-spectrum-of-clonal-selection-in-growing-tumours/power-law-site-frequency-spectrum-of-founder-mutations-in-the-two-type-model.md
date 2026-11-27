# Power-law site frequency spectrum of founder mutations in the two-type model

**Model.** Type-0 tumour cells divide at rate $a_0$ and die at rate $b_0$, with $\lambda_0=a_0-b_0>0$; each type-0 cell mutates to an advantageous type 1 at rate $u_1$, and type-1 cells grow with net rate $\lambda_1>\lambda_0$. Every cell also acquires neutral mutations at rate $\nu$ during its lifetime (infinitely many sites). Idealise the type-0 population as $Z_0^*(t)=V_0e^{\lambda_0t}$ for all $t\in\mathbb R$, with $V_0$ exponential of rate $\lambda_0/a_0$, and take $a_0=a_1=1$. Let $\alpha=\lambda_0/\lambda_1\in(0,1)$ and let $s_{1/2}=\lambda_0^{-1}\log\big(\lambda_0^2/(u_1\lambda_1)\big)$ be the median time of the first type-1 mutation whose lineage survives.

1. **Type-1 population.** As $t\to\infty$, $e^{-\lambda_1(t-s_{1/2})}Z_1^*(t)\to\bar V_1$, where $\bar V_1$ is the sum of the points of a Poisson process on $(0,\infty)$ with mean measure $\bar\rho(x,\infty)=c_\alpha V_0\,x^{-\alpha}$; the constant $c_\alpha$ depends on $\lambda_0,\lambda_1$ only, not on $u_1$. Each point is the contribution of one type-1 family (one founding advantageous mutation).
2. **Neutral mutations inside type 1.** The number of neutral mutations arising in type-1 cells that reach frequency at least $f$ within the type-1 population is asymptotically $\nu/(\lambda_1f)$, a $1/f$ law; the same $1/f$ law holds for neutral mutations of a single exponentially growing type.
3. **Founder (type 1A) mutations.** Since the Poisson points divided by their sum have the Poisson–Dirichlet law $\mathrm{PD}(\alpha,0)$, the expected number of advantageous founder mutations with frequency at least $f$ in the type-1 population is

    $$\mathrm{SFS}_{1A}(f)=\frac{\sin(\pi\alpha)}{\pi\alpha}\Big(\frac1f-1\Big)^{\alpha},\qquad 0<f<1,$$

    which equals $(2/\pi)(1/f-1)^{1/2}$ for $\alpha=1/2$. Neutral type-0 mutations carried by the founders do not change this $f^{-\alpha}$ shape.

Hence under clonal selection the high-frequency part of the spectrum decays like $f^{-\lambda_0/\lambda_1}$ rather than $f^{-1}$, so a neutral exponentially growing tumour is distinguishable from the two-type model by the shape of its site frequency spectrum.

## Expansion

For the $1/f$ law: mutations accumulate at rate $\nu N(s)$ with $N(s)\approx\bar Ve^{\lambda s}$, so by time $t$ there are about $\nu\bar Ve^{\lambda t}/\lambda$ of them, and a mutation that arose when the population had size $N$ ends at frequency about $1/N$; those at frequency at least $f$ arose before $N=1/f$, giving $\nu/(\lambda f)$. For founders, a successful type-1 mutation arising at time $s$ grows to $W e^{\lambda_1(t-s)}$ with $W$ exponential, and mutations arrive at rate proportional to $e^{\lambda_0 s}$; the image of this Poisson process under $s\mapsto We^{-\lambda_1s}$ has intensity proportional to $x^{-\alpha-1}dx$. Ranked normalised points of a Poisson process with intensity $x^{-\alpha-1}$ follow $\mathrm{PD}(\alpha,0)$ (Pitman–Yor), whose expected count of masses at least $f$ gives the displayed formula. The largest families arise within a few multiples of $1/\lambda_1$ after the first one, so they carry roughly the same number of type-0 passengers.

## Sources

- H.-R. Tung, R. Durrett, "Signatures of neutral evolution in exponentially growing tumors: A theoretical perspective", PLoS Computational Biology 17 (2021) e1008701, Limit theorems (Eqs. (2)–(3), Theorem 1), Site frequency spectrum (Theorem 2, Eq. (4)), Methods (Theorem 3, Eqs. (7)–(8), proof of Theorem 2), <https://doi.org/10.1371/journal.pcbi.1008701>, PMCID PMC7904140.
