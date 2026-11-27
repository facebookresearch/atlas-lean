# STAAR omnibus test by Cauchy combination

Given the p-values $p_{\mathrm{Burden},k}, p_{\mathrm{SKAT},k}, p_{\mathrm{ACAT\text{-}V},k}$ ($k = 0, \dots, K$) of the [annotation-weighted statistics](annotation-weighted-burden-skat-and-acat-v-statistics.md), define for each test type, e.g. burden,

$$T_{\mathrm{STAAR\text{-}B}} = \frac{1}{K+1} \sum_{k=0}^{K} \tan\big((0.5 - p_{\mathrm{Burden},k})\pi\big), \qquad p_{\mathrm{STAAR\text{-}B}} \approx \frac12 - \frac{\arctan(T_{\mathrm{STAAR\text{-}B}})}{\pi},$$

and likewise STAAR-S and STAAR-A from the SKAT and ACAT-V p-values. For a set $\mathcal{A}$ of Beta-weight parameters $(a_1, a_2)$ (in practice $\{(1, 25), (1, 1)\}$), the omnibus statistic is

$$T_{\mathrm{STAAR\text{-}O}} = \frac{1}{3|\mathcal{A}|} \sum_{(a_1,a_2) \in \mathcal{A}} \Big[\tan\big((0.5 - p_{\mathrm{STAAR\text{-}B}}^{(a_1,a_2)})\pi\big) + \tan\big((0.5 - p_{\mathrm{STAAR\text{-}S}}^{(a_1,a_2)})\pi\big) + \tan\big((0.5 - p_{\mathrm{STAAR\text{-}A}}^{(a_1,a_2)})\pi\big)\Big],$$

with $p_{\mathrm{STAAR\text{-}O}} \approx \tfrac12 - \arctan(T_{\mathrm{STAAR\text{-}O}})/\pi$.

## Depends on

- [Annotation-weighted burden, SKAT and ACAT-V statistics](annotation-weighted-burden-skat-and-acat-v-statistics.md)

## Expansion

If $p$ is uniform on $(0,1)$ then $\tan((0.5 - p)\pi)$ is standard Cauchy, and $\tfrac12 - \arctan(t)/\pi$ is the standard Cauchy upper tail at $t$. For independent p-values an average of standard Cauchy variables is again exactly standard Cauchy (stability of the Cauchy law), so the combined p-value is exact; for the strongly dependent p-values produced by reusing the same scores under different weights, the Cauchy tail approximation remains accurate at small significance levels, which is why no permutation is needed. The omnibus combines tests with complementary power: burden when most variants are causal with effects in one direction, SKAT when effects have mixed signs, and ACAT-V when few variants, or many extremely rare ones, are causal.

## Sources

- X. Li, Z. Li, H. Zhou et al., "Dynamic incorporation of multiple in silico functional annotations empowers rare variant association analysis of large whole-genome sequencing studies at scale", Nature Genetics 52 (2020), <https://doi.org/10.1038/s41588-020-0676-4> (PMC7483769). Online Methods.
