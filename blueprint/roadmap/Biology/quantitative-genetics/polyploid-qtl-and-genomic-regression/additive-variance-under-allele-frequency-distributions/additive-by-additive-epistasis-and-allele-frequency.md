# Additive-by-additive epistasis and allele frequency

**Model.** Two unlinked biallelic loci $B$ and $C$ in linkage equilibrium and Hardy–Weinberg proportions, with frequencies $p$ of $B$ and $q$ of $C$ and heterozygosities $H_p = 2p(1-p)$, $H_q = 2q(1-q)$. Code genotypes by $x_B, x_C \in \{+1, 0, -1\}$ (homozygote $BB$, heterozygote, homozygote $bb$, and likewise for $C$) and take genotypic values

$$G = a\,(1 + x_Bx_C),$$

so $BBCC$ and $bbcc$ have value $2a$, $BBcc$ and $bbCC$ have value $0$, and every genotype heterozygous at either locus has value $a$.

**Proposition.**

$$M = 2a\,[pq + (1-p)(1-q)],\qquad V_A = a^2(H_p + H_q - 4H_pH_q),\qquad V_{AA} = a^2H_pH_q,\qquad V_G = a^2(H_p + H_q - 3H_pH_q),$$

so

$$\frac{V_A}{V_G} = 1 - \frac{H_pH_q}{H_p + H_q - 3H_pH_q}.$$

The additive fraction is $0$ at $p = q = 1/2$ (all variance epistatic) and tends to $1$ as either locus approaches fixation; with $p = q = 0.1, 0.2, 0.3, 0.4$ it is about $0.88, 0.69, 0.43, 0.14$. Averaged over allele frequencies, $\mathbb E V_A = 2a^2/9$, $\mathbb E V_{AA} = a^2/9$ and $\eta^2 = \mathbb E V_A/\mathbb E V_G = 2/3$ for independent uniform $p, q$, while for the neutral U-shaped distribution $\eta^2 = (2 - 4/K)/(2 - 3/K)$ with $K \approx \ln(2N)$, which tends to $1$ as $N$ grows.

## Depends on

- [Additive variance at a biallelic locus](../../fisher-s-decomposition-of-genetic-variance/add-var-biallelic.md)
- [Expected additive fraction at a locus with dominance](expected-additive-fraction-at-a-locus-with-dominance.md)

## Expansion

With independence, $\mathbb E x_B = 2p - 1$ and $\mathbb E x_B^2 = 1 - H_p$, so $V_G = a^2\operatorname{Var}(x_Bx_C) = a^2[(1-H_p)(1-H_q) - (1-2H_p)(1-2H_q)] = a^2(H_p + H_q - 3H_pH_q)$, and $M = a[1 + (2p-1)(2q-1)]$, which equals the displayed mean. The average effect of substituting $B$ is $\tfrac12\partial M/\partial p = a(2q - 1)$, so $V_A = 2p(1-p)\,a^2(1-2q)^2 + 2q(1-q)\,a^2(1-2p)^2$, which rewrites as $a^2(H_p + H_q - 4H_pH_q)$ using $(1-2p)^2 = 1 - 2H_p$. The additive-by-additive effect is $\tfrac14\partial^2M/\partial p\,\partial q = a$, giving $V_{AA} = 4a^2p(1-p)q(1-q) = a^2H_pH_q$, and $V_A + V_{AA} = V_G$ since there is no dominance. A locus at an extreme frequency makes the other locus's effect almost constant across the population, so its contribution becomes additive.

## Sources

- W. G. Hill, M. E. Goddard and P. M. Visscher, "Data and theory point to mainly additive genetic variance for complex traits", PLoS Genetics 4 (2008), e1000008, Theory ("Additive × Additive Model") and Results ("Two Locus Additive × Additive Model"), <https://doi.org/10.1371/journal.pgen.1000008> (PMC2265475).
