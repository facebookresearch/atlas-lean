# Background selection with recombination and a distribution of selection strengths

Consider a neutral site $n$ in a genome where purifying selection acts at sites $x$, multiplicatively across sites and strongly enough that deleterious alleles stay rare (so homozygotes for them can be ignored). Let $u_x$ be the haploid deleterious mutation rate per generation at $x$, $r_{x,n}$ the recombination rate per generation between $x$ and $n$, and let the heterozygous fitness of a deleterious allele be $1 - t$ with $t \in (0, 1]$ drawn from a probability density $f_x$. The expected reduction of neutral diversity at $n$ is

$$B(n) = \frac{\pi_e}{\pi_0} = \frac{N_e}{N_0} \approx \exp\Biggl(-\sum_{x} \int_0^1 \frac{u_x\, f_x(t)}{t\,\bigl(1 + (1 - t)\, r_{x,n} / t\bigr)^2}\, dt\Biggr),$$

where $\pi_e$, $N_e$ are the expected diversity and effective size at $n$ and $\pi_0$, $N_0$ their values without background selection. If the selected sites split into classes with their own $u$ and $f$ (exonic and non-exonic conserved segments in the paper), the sum splits and $B = B_{\mathrm{ex}} B_{\mathrm{nex}}$. For an X-linked site, $t = t_m/3 + 2 t_f/3$, with $t_m$ and $t_f$ the selection strengths in hemizygous males and heterozygous females.

## Depends on

- [Background selection reduces the effective size to the mutation-free class](background-selection-deterministic-reduction-fac.md)

## Proof depends on

- [Background selection reduces the effective size to the mutation-free class](background-selection-deterministic-reduction-fac.md)

## Expansion

This is the Hudson–Kaplan and Nordborg–Charlesworth–Charlesworth approximation, averaged over a distribution of selection strengths. Each selected site contributes $u_x t / (t + (1-t) r_{x,n})^2$; with no recombination ($r_{x,n} = 0$) and a point mass at $t$ the exponent is $-\sum_x u_x / t = -U/t$, the reduction to the mutation-free class. Recombination shrinks each contribution roughly as $u_x t / r_{x,n}^2$ once $r_{x,n} \gg t$. The paper evaluates $B$ genome-wide from a fine-scale recombination map with truncated exponential or gamma densities $f$ and fits $u$ and the mean of $f$ by maximum likelihood to primate divergence data.

## Sources

- G. McVicker et al., *Widespread genomic signatures of natural selection in hominid evolution*, PLoS Genet. 5 (2009), e1000471. <https://doi.org/10.1371/journal.pgen.1000471> (PMCID: PMC2669884), Methods, "Background Selection".
