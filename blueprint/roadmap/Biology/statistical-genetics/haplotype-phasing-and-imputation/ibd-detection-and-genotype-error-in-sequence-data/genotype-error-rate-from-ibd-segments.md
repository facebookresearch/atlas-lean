# Estimating the genotype error rate from IBD segments

At a low-frequency biallelic variant with major allele $A$ and minor allele $B$, let $\gamma$ be the rate at which true $AA$ genotypes are reported as $AB$; assume $\gamma$ is small, $p_A$ is close to $1$, and errors at true $AB$ or $BB$ genotypes and double errors are negligible. Write $f_{AA}, f_{AB}$ for the observed (error-added) genotype frequencies and $f_A = f_{AA} + f_{AB}/2$ for the observed major allele frequency. Then the true frequencies satisfy, to first order in $\gamma$,

$$p_{AA} \approx f_{AA}(1 + \gamma), \qquad p_{AB} \approx f_{AB} - f_{AA}\gamma, \qquad p_A \approx f_A + \tfrac12 f_{AA}\gamma .$$

For two individuals sharing one allele identical by descent, the probability that one is observed $AA$ and the other $AB$ (unordered) is, to first order in $\gamma$,

$$P_{\mathrm{Obs}}(AA, AB) \approx \frac{f_{AA} f_{AB}}{f_A} + \frac{f_{AA}^2}{f_A^2}\left(f_A - \frac{f_{AB}}{2}\right)\gamma,$$

so

$$\gamma \approx \frac{f_A^2\, P_{\mathrm{Obs}}(AA, AB) - f_A f_{AA} f_{AB}}{f_{AA}^2 \left(f_A - \tfrac12 f_{AB}\right)} .$$

**Estimator (SEQERR).** Over variants $i$ in a frequency class and IBD pairs $j$, let $I^{(i,j)}(AA, AB)$ indicate that pair $j$ shows the $AA/AB$ configuration at variant $i$ inside a detected IBD segment, and let $\hat f$ denote observed frequencies at variant $i$. Then

$$\hat\gamma = \frac{\sum_j \sum_i \left(\hat f_A(i)^2\, I^{(i,j)}(AA, AB) - \hat f_A(i)\, \hat f_{AA}(i)\, \hat f_{AB}(i)\right)}{\sum_j \sum_i \hat f_{AA}(i)^2 \left(\hat f_A(i) - \tfrac12 \hat f_{AB}(i)\right)} .$$

Under near Hardy–Weinberg proportions this says that without error the $AA/AB$ configuration appears in IBD pairs at rate about $2 f_B$, while with error it appears at about $2 f_B + \gamma$.

## Proof sketch

From $f_{AA} \approx p_{AA}(1-\gamma)$ and $f_{AB} \approx p_{AB} + p_{AA}\gamma$ one inverts to the true frequencies. Two IBD individuals carry the shared allele plus one non-shared allele each, so $P_{\mathrm{True}}(AA, AB) = 2\, p_{AA}\, p_{AB}/(2 p_A)$ and $P_{\mathrm{True}}(AA, AA) = p_{AA}^2 / p_A$. The observed $AA/AB$ configuration arises from a true $AA/AB$ pair with no error (probability about $1 - \gamma$) or from a true $AA/AA$ pair with one error (probability about $2\gamma$); substituting the inverted frequencies and keeping first-order terms in $\gamma$ gives the displayed relation, and solving for $\gamma$ gives the moment estimator, which pools numerator and denominator over variants and pairs. The intuitive version: almost all genotypes are $AA$, so $f_B \approx p_B + \gamma/2$, and the $AA/AB$ rate rises from $2p_B$ to $2p_B + 2\gamma = 2 f_B + \gamma$. Reliable IBD is essential: only segments longer than $2$ cM, with $0.5$ cM trimmed from each end, are used. On simulated data the estimates tracked the true error rate closely, and on interim UK10K data they agreed with half the discordance rate of duplicate pairs.

## Depends on

- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Proof depends on

- [Single-marker IBD LOD score under independent allele errors](single-marker-ibd-lod-score-with-allele-errors.md)

## Sources

- B. L. Browning and S. R. Browning, "Detecting identity by descent and estimating genotype error rates in sequence data", The American Journal of Human Genetics 93 (2013), 840–851, Material and Methods ("Genotype Error Rate Estimation") and Appendix B (Equations B1–B2), <https://doi.org/10.1016/j.ajhg.2013.09.014> (PMC3824133).
