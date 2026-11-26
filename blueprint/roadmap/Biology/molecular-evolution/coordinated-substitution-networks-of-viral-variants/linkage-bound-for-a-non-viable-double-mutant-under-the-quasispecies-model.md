# Linkage bound for a non-viable double mutant under the quasispecies model

**Model.** Fix two loci $u,v$ with alleles $0$ (reference) and $1$ (alternative), and let $E^t_{ij}$ be the expected count of 2-haplotype $(i,j)$ at time $t$. Each 2-haplotype has fitness $f_{ij}\ge0$, and allele $k$ mutates to $l$ at locus $u$ (resp. $v$) with probability $q^u_{kl}$ (resp. $q^v_{kl}$). The expected counts follow the quasispecies (mutation–selection) recursion

$$E^t_{ij}=\sum_{k,l\in\{0,1\}}f_{kl}\,q^u_{ki}\,q^v_{lj}\,E^{t-1}_{kl},$$

and mutation is rarer than no change: $0<q^u_{ij}<q^u_{ii}$ and $0<q^v_{ij}<q^v_{ii}$ for $i\ne j$.

**Theorem.** If the double mutant is non-viable, $f_{11}=0$, then

$$E^t_{11}\le\frac{E^t_{01}\,E^t_{10}}{E^t_{00}} .$$

**Linkage test.** Suppose that $N$ genomes are sampled, that $O^t_{ij}$ are the observed 2-haplotype counts, and that the number of genomes carrying $(1,1)$ is $X\sim\mathrm{Bin}(N,q)$. The theorem gives $q\le p=O^t_{10}O^t_{01}/(O^t_{00}N)$, and hence

$$P\bigl(X\ge O^t_{11}\mid f_{11}=0\bigr)\le 1-F_{\mathrm{Bin}(N,p)}\bigl(O^t_{11}-1\bigr).$$

The loci are declared linked (the double mutant is viable, i.e. the pair is not under negative epistasis) when this upper bound is at most $\rho/L^2$: a Bonferroni-corrected level $\rho$ over the $L^2$ tested pairs. The resulting graph on single-amino-acid variants is the coordinated substitution network $G_t$.

## Depends on

- [Bonferroni rejection set](../../../Probability/hypothesis-testing/bonferroni-correction/bonferroni-rejections.md)

## Expansion

Expand $E^t_{00}E^t_{11}$ and $E^t_{01}E^t_{10}$ as quadratic forms in $(f_{00}E^{t-1}_{00},f_{10}E^{t-1}_{10},f_{01}E^{t-1}_{01})$, which is possible because the $f_{11}$ terms vanish. All coefficients agree except those of the cross term $f_{01}f_{10}E^{t-1}_{01}E^{t-1}_{10}$. Their difference factors as

$$\Bigl(1-\tfrac{q^u_{01}q^u_{10}}{q^u_{00}q^u_{11}}\Bigr)\Bigl(1-\tfrac{q^v_{01}q^v_{10}}{q^v_{00}q^v_{11}}\Bigr)q^u_{00}q^v_{11}q^u_{11}q^v_{00}\,f_{01}f_{10}E^{t-1}_{01}E^{t-1}_{10}\ \ge0,$$

and it is nonnegative because mutation probabilities are below no-change probabilities. The bound states that a lethal double mutant cannot show positive linkage disequilibrium. An observed excess of $(1,1)$ beyond the product ratio is therefore evidence that the pair is viable. The binomial tail is monotone in $q$, so the observable bound $p$ gives a conservative test.

## Sources

- F. Mohebbi, A. Zelikovsky, S. Mangul, G. Chowell, P. Skums, "Early detection of emerging viral variants through analysis of community structure of coordinated substitution networks", *Nature Communications* 15:2838 (2024), Methods, "Inference of coordinated substitution networks", Eqs. (3)–(12), Theorem 1, <https://doi.org/10.1038/s41467-024-47304-6>, PMCID PMC10987511.
