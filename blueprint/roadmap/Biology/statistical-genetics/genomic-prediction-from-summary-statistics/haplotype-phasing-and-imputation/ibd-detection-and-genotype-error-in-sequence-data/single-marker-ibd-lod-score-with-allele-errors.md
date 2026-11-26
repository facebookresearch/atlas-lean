# Single-marker IBD LOD score under independent allele errors

At a biallelic marker with major allele $A$ and minor allele $B$, let $p_A, p_B$ be the true allele frequencies and suppose each observed allele is miscalled independently with probability $\varepsilon \ge 0$. The error-added frequencies are then

$$f_B = (1 - \varepsilon)\, p_B + \varepsilon\, (1 - p_B) = p_B (1 - 2\varepsilon) + \varepsilon, \qquad\text{so}\qquad p_B = \frac{f_B - \varepsilon}{1 - 2\varepsilon},$$

which lets $p_B$ be estimated from the observed frequency $f_B$.

For two ordered, non-inbred individuals under Hardy–Weinberg equilibrium, the **IBD model** has exactly one allele shared identical by descent, so the pair carries three independent alleles; without error,

$$P(AA, AA \mid I) = p_A^3,\quad P(AA, AB \mid I) = p_A^2 p_B,\quad P(AB, AB \mid I) = p_A p_B,\quad P(AA, BB \mid I) = 0,$$

and symmetrically $P(AB, BB \mid I) = p_A p_B^2$, $P(BB, BB \mid I) = p_B^3$. With errors, writing $e_j = \varepsilon^j (1 - \varepsilon)^{4 - j}$ for the probability of a given pattern of $j$ errors among the four observed alleles, and dropping negligible higher-order terms, the observed-pair probabilities include

$$P_O(AA, AA \mid I) \approx e_0 p_A^3 + 2 e_1 p_A^2 p_B + e_2 p_A p_B,$$

$$P_O(AA, AB \mid I) \approx e_0 p_A^2 p_B + (e_1 + 3 e_2)\, p_A p_B + 2 e_1 p_A^3,$$

$$P_O(AA, BB \mid I) = (e_1 + e_2 + e_3)\, p_A p_B + e_2 (p_A^3 + p_B^3),$$

$$P_O(AB, AB \mid I) \approx (e_0 + 4 e_1 + 2 e_2)\, p_A p_B + 4 e_2 (p_A^3 + p_B^3),$$

with the remaining cases obtained by exchanging the roles of $A$ and $B$. The **non-IBD model** treats the four alleles as independent with the observed frequencies: $P_O(AA) \approx f_A^2$, $P_O(AB) \approx 2 f_A f_B$, $P_O(BB) \approx f_B^2$, and the pair probability is the product.

The **single-marker IBD LOD score** is

$$\mathrm{LOD} = \log_{10} \frac{P_O(g_1, g_2 \mid I)}{P_O(g_1)\, P_O(g_2)},$$

set to $0$ if any allele is missing. An IBD segment is reported for a pair on every maximal interval whose summed LOD exceeds a threshold (for example $3$), which can be found by a single linear scan; summing LODs multiplies likelihood ratios, so markers are first thinned to approximate linkage equilibrium.

## Remarks

Without error, opposite homozygotes $(AA, BB)$ are impossible under IBD, so a single error would veto a true segment; the error model replaces that zero by a term of order $\varepsilon$, so discordant homozygotes give strong but finite evidence against IBD. Each observed-pair probability sums the true-pair probabilities times the probabilities of the error patterns that map one to the other; for example $(AA, AA)$ is observed from true $(AA, AA)$ with no error, from $(AA, AB)$ or $(AB, AA)$ with one error, and from $(AB, AB)$ with two. Markers removed by LD thinning still contribute negative evidence: their LOD is used only when the genotypes are discordant homozygotes, which lowers false positives without double-counting positive evidence. In IBDseq the analysis error rate is frequency-dependent, $\varepsilon = \min\{\sigma, \rho f_B\}$ with $\rho = 0.25$ and $\sigma$ between $0.001$ and $0.005$; performance was insensitive to $\sigma$ as long as $\sigma > 0$. The same construction with a homozygosity-by-descent model gives a detector of autozygous segments.

## Depends on

- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- B. L. Browning and S. R. Browning, "Detecting identity by descent and estimating genotype error rates in sequence data", The American Journal of Human Genetics 93 (2013), 840–851, Material and Methods ("IBD LOD Score", "Analysis Allele Error Rate"), Table 1 and Appendix A, <https://doi.org/10.1016/j.ajhg.2013.09.014> (PMC3824133).
