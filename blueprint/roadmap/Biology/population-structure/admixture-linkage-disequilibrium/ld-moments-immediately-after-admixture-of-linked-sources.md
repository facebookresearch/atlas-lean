# LD moments immediately after admixture of populations already in LD

Let source populations $1$ and $2$ have two-locus gamete frequencies $x^{(1)}$ and $x^{(2)}$, allele frequencies $p_i$ at locus $A$ and $q_i$ at locus $B$, and linkage disequilibria $D_i = x^{(i)}_{AB} - p_i q_i$. An admixed population formed in one pulse takes a fraction $f \in [0,1]$ of its gametes from population $1$ and $1-f$ from population $2$, so its gamete frequencies are $f x^{(1)} + (1-f)x^{(2)}$. Write $\delta = (p_1 - p_2)(q_1 - q_2)$. Immediately after the pulse its disequilibrium is

$$D_{\mathrm{adm}} = f D_1 + (1-f) D_2 + f(1-f)\,\delta,$$

and therefore

$$D_{\mathrm{adm}}^2 = f^2 D_1^2 + (1-f)^2 D_2^2 + 2f(1-f) D_1 D_2 + 2f^2(1-f) D_1\delta + 2f(1-f)^2 D_2\delta + f^2(1-f)^2\delta^2 .$$

Taking expectations over the random source frequencies gives $\mathbb{E}[D_{\mathrm{adm}}]$ and $\mathbb{E}[D_{\mathrm{adm}}^2]$ in terms of the source moments $\mathbb{E}[D_i]$, $\mathbb{E}[D_i^2]$, $\mathbb{E}[D_1D_2]$, $\mathbb{E}[D_i\delta]$ and $\mathbb{E}[\delta^2]$. These are the initial conditions for continuing the two-locus moment recursion in the admixed population. When $D_1 = D_2 = 0$ the first identity reduces to the Chakraborty–Weiss admixture disequilibrium.

## Proof sketch

The admixed allele frequencies are $p = fp_1 + (1-f)p_2$ and $q = fq_1 + (1-f)q_2$, and its $AB$ frequency is $f(D_1 + p_1q_1) + (1-f)(D_2 + p_2q_2)$. Expanding $pq = f^2p_1q_1 + f(1-f)(p_1q_2 + p_2q_1) + (1-f)^2p_2q_2$ and subtracting it leaves $fD_1 + (1-f)D_2 + f(1-f)(p_1q_1 + p_2q_2 - p_1q_2 - p_2q_1)$, and the last bracket is $\delta$. The second identity is the square of the first. In expectation, the cross term $\mathbb{E}[D_1D_2]$ is the cross-population covariance that the multi-population recursion tracks from the split.

## Depends on

- [Admixture linkage disequilibrium right after the pulse](linkage-diseq-source-mix.md)

## Sources

- A. P. Ragsdale, S. Gravel, *Models of archaic admixture and recent history from two-locus statistics*, PLoS Genetics 15 (2019), e1008204, <https://doi.org/10.1371/journal.pgen.1008204>, PMCID PMC6586359. Admixture moments Eqs. (7)–(8).
