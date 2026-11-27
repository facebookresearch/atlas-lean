# Neutral copy-number distribution under unequal recombination

**Model.** In an infinite population, each chromosome carries $y' \ge 1$ tandem copies of a gene; $p_t(y')$ is the frequency of chromosomes with $y'$ copies. Each generation a pair of chromosomes with $y'_m$, $y'_p$ copies is drawn (by fitness; at random under neutrality). With probability $1 - r$ one parental chromosome is transmitted unchanged; with probability $r$ unequal recombination marks a uniformly random copy on each and fuses the head of one with the tail of the other, so the offspring copy number is

$$Y' = B_1 + B_2 - 1, \qquad B_1 \sim \mathrm{Unif}\{1,\dots,y'_m\},\ B_2 \sim \mathrm{Unif}\{1,\dots,y'_p\},$$

a trapezoidal law $T(\,\cdot\,; y'_m, y'_p)$ on $\{1, \dots, y'_m + y'_p - 1\}$. Under neutrality

$$p_{t+1}(y') = (1 - r)\,p_t(y') + r\sum_{y'_1, y'_2} p_t(y'_1)p_t(y'_2)\,T(y'; y'_1, y'_2).$$

**Theorem.** Under neutrality:
1. the mean copy number per chromosome $E[Y']$ is conserved, since $E[B_1 + B_2 - 1] = (y'_m + y'_p)/2$;
2. for every $a > 0$ the distribution

$$p_{\mathrm{stat}}(y') = \frac{(e^{a} - 1)^2}{e^{a}}\; y'\, e^{-a y'}, \qquad y' = 1, 2, \dots,$$

the discrete kernel of a Gamma law with shape $2$, is stationary for every $r > 0$, and $a$ is pinned by the conserved mean, $\coth(a/2) = E[Y']$, so $a \approx 2/E[Y']$ for large arrays.

Consequently the copy number of a diploid individual, the sum of two independent chromosomes, has stationary law proportional to $(y^3 - y)\,e^{-a y}/6$, $y \ge 2$, a discrete Gamma kernel of shape $4$.

## Expansion

Stationarity does not depend on $r$ because the recombination step must map $p_{\mathrm{stat}}$ to itself; splitting the convolution with the trapezoidal kernel into the regions where $y'$ lies below, between or above $y'_1 \wedge y'_2$ and $y'_1 \vee y'_2$ and summing the geometric series gives back $y' e^{-a y'}$ times the normalizing constant. The mean of $y' e^{-a y'}$ is $(1 + e^{-a})/(1 - e^{-a}) = \coth(a/2)$. Otto et al.'s Proposition 1 states the large-array form, writing $a = 2/E[Y']$; the exact relation $\coth(a/2) = E[Y']$ holds for every $a > 0$, and $\coth(a/2) = 2/a + O(a)$ as $a \to 0$ recovers it. Selection on copy number shifts the mean and narrows the law; fitting the Gamma approximation to human copy-number data for tandemly arrayed genes gives estimates of recombination and selection.

## Sources

- M. Otto, Y. Zheng, T. Wiehe, "Recombination, selection, and the evolution of tandem gene arrays", Genetics 221(3) (2022) iyac052, Methods (trapezoidal recombination kernel), equation (4), Proposition 1 with equation (5) and its proof in the Appendix, <https://doi.org/10.1093/genetics/iyac052>, PMCID: PMC9252282.
