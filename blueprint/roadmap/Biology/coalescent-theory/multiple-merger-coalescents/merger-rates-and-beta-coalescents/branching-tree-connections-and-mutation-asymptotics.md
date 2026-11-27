# Beta-coalescents, stable trees and frequency spectra of large samples

Berestycki, Berestycki and Schweinsberg (2007) embed the $\mathrm{Beta}(2 - \alpha, \alpha)$-coalescent, $1 < \alpha < 2$, in continuous stable random trees, using a result of Birkner et al. and a construction of the Donnelly–Kurtz lookdown process from continuous random trees, and derive small-time and large-sample results. For mutations at rate $\theta$ on the genealogy of a sample of size $n$, let $M_k(n)$ be the number of mutations carried by exactly $k$ sampled individuals (infinite sites) and $N_k(n)$ the number of allelic types carried by exactly $k$ individuals (infinite alleles). Their Theorem 9 gives, for each fixed $k$, as $n \to \infty$,

$$n^{\alpha - 2} M_k(n) \to \theta\alpha(\alpha - 1)^2 \frac{\Gamma(k + \alpha - 2)}{k!}, \qquad n^{\alpha - 2} N_k(n) \to \theta\alpha(\alpha - 1)^2 \frac{\Gamma(k + \alpha - 2)}{k!}$$

in probability, and the total number of mutations and the total branch length $L_n$ satisfy $n^{\alpha - 2}M(n) \to \theta\alpha(\alpha - 1)\Gamma(\alpha)/(2 - \alpha)$ (equation (9), in Remark 10) and $n^{\alpha - 2}L_n \to \alpha(\alpha - 1)\Gamma(\alpha)/(2 - \alpha)$ (Theorem 1.9 of Berestycki, Berestycki and Schweinsberg 2008, as recalled in the proof of Theorem 9), both in probability; so these quantities grow like $n^{2 - \alpha}$. The proof approximates the coalescent at small times by a continuous-time Galton–Watson process with exponential lifetimes and offspring law $P(\chi = k) = \alpha\Gamma(k - \alpha)/(k!\,\Gamma(2 - \alpha))$, $k \ge 2$ (equation (10)). For finite samples, Birkner, Blath and Eldon (2013) derive recursions for the expected value, variance and covariance of the site-frequency spectrum under a general $\Lambda$-coalescent, extending Fu's results for Kingman's coalescent.

## Depends on

- [The Beta-coalescent measure on the unit interval](beta-lambda.md)
- [The Λ-coalescent on the natural numbers](../speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Expansion

1. The Beta-coalescent and its embedding in the continuous stable random tree through the lookdown construction.
2. The small-time approximation by the Galton–Watson process with offspring law (10).
3. The total number of mutations (equation (9)) and the total branch length (Theorem 1.9 of Berestycki, Berestycki and Schweinsberg 2008), of order $n^{2-\alpha}$.
4. The site- and allele-frequency spectra for fixed $k$ (Theorem 9).
5. The recursions of Birkner, Blath and Eldon for the moments of the spectrum of a $\Lambda$-coalescent, as a separate statement.

## Sources

- J. Berestycki, N. Berestycki and J. Schweinsberg, Beta-coalescents and continuous stable random trees, Ann. Probab. 35 (2007), 1835–1887, abstract, Theorem 9, Remark 10 (equations (9), (10)) and Section 6. <https://doi.org/10.1214/009117906000001114>
- J. Berestycki, N. Berestycki and J. Schweinsberg, Small-time behavior of beta coalescents, Ann. Inst. Henri Poincaré Probab. Stat. 44 (2008), 214–238, Theorem 1.9. <https://doi.org/10.1214/07-AIHP103>
- M. Birkner, J. Blath and B. Eldon, Statistical properties of the site-frequency spectrum associated with Λ-coalescents, Genetics 195 (2013), 1037–1053, abstract. <https://doi.org/10.1534/genetics.113.156612>
