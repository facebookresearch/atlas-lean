# Expected additive fraction at a locus with dominance

**Setting.** A biallelic locus has genotypic values $+a$, $d$, $-a$ for $CC$, $Cc$, $cc$, Hardy–Weinberg proportions and frequency $p$ of $C$. Then

$$V_A(p) = 2p(1-p)\,[a + d(1-2p)]^2,\qquad V_D(p) = 4p^2(1-p)^2d^2,\qquad V_G = V_A + V_D .$$

Average over a distribution $f$ of $p$ across loci and write $\eta^2 = \mathbb E V_A/\mathbb E V_G$.

**Proposition.**

1. *Uniform distribution* $f(p) = 1$ on $[0,1]$:

$$\mathbb E V_A = \frac{a^2}{3} + \frac{d^2}{15},\qquad \mathbb E V_D = \frac{2d^2}{15},\qquad \eta^2 = 1 - \frac{2d^2}{5a^2 + 3d^2}.$$

2. *Neutral U-shaped distribution* $f(p) = \dfrac{1}{2K\,p(1-p)}$ on $\big[\tfrac1{2N}, 1-\tfrac1{2N}\big]$ with $K \approx \ln(2N)$, ignoring $O(1/N)$ terms:

$$\mathbb E V_A \approx \frac{a^2 + d^2/3}{K},\qquad \mathbb E V_D \approx \frac{d^2}{3K},\qquad \eta^2 = 1 - \frac{d^2}{3a^2 + 2d^2}.$$

3. *Complete dominance* ($d = a$): $V_A/V_G = 2/3$ at $p = 1/2$, but $\eta^2 = 0.75$ under the uniform and $\eta^2 = 0.8$ under the U-shaped distribution; as the dominant allele becomes rare ($p \to 0$), $V_A/V_G \to 1$. Even for pure overdominance ($a = 0$) all genetic variance becomes additive at extreme frequencies.

## Depends on

- [Additive variance at a biallelic locus](../../../fisher-s-decomposition-of-genetic-variance/add-var-biallelic.md)
- [Dominance variance at a biallelic locus](../../../fisher-s-decomposition-of-genetic-variance/dom-var-biallelic.md)
- [Fisher's variance decomposition](../../../fisher-s-decomposition-of-genetic-variance/gen-var-eq-add-var-add-dom-var.md)

## Expansion

Use $\int_0^1 p(1-p)\,dp = 1/6$, $\int_0^1 p(1-p)(1-2p)\,dp = 0$, $\int_0^1 p(1-p)(1-2p)^2\,dp = 1/30$ and $\int_0^1 p^2(1-p)^2\,dp = 1/30$ for part 1. Under the U-shaped density the factor $p(1-p)$ in $V_A$ cancels, leaving $\frac1K\int(a + d(1-2p))^2dp = (a^2 + d^2/3)/K$, while $V_D$ keeps one factor $p(1-p)$ and gives $d^2/(3K)$. The mechanism is that when one allele is rare almost all individuals are heterozygotes or common homozygotes, so the regression of genotypic value on allele count fits the genotypic values almost exactly. Since neutral and nearly neutral variants are concentrated at extreme frequencies, high narrow-sense heritability is the expected outcome even when gene action is far from additive.

## Sources

- W. G. Hill, M. E. Goddard and P. M. Visscher, "Data and theory point to mainly additive genetic variance for complex traits", PLoS Genetics 4 (2008), e1000008, Theory ("Single Locus with Arbitrary Dominance") and Results, <https://doi.org/10.1371/journal.pgen.1000008> (PMC2265475).
