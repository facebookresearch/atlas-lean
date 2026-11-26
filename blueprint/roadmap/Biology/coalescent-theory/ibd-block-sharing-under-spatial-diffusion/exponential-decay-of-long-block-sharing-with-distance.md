# Exponential decay of long-block sharing with distance

In the model of [expected IBD block sharing under two-dimensional diffusion of ancestry](expected-ibd-block-sharing-under-spatial-diffusion.md) with power-law density $D_e(t) = D t^{-\beta}$, fix a block length $L > 0$. As the sample distance $r \to \infty$,

$$\mathbb{E}[N_L] \sim C_{L,\beta}\, r^{\frac{3}{2} + \beta} \exp\!\left(-\frac{\sqrt{2L}}{\sigma}\, r\right), \qquad C_{L,\beta} = 2^{-\frac{3\beta}{2} - 3} \frac{G}{\pi D \sigma^2} (\sqrt{L}\,\sigma)^{-(2+\beta)} \sqrt{\frac{\pi \sigma}{2\sqrt{2L}}},$$

so that $\frac{d}{dr} \log \mathbb{E}[N_L] \to -\sqrt{2L}/\sigma$. The limiting slope does not depend on $D$ or $\beta$, and the same holds for any density history that is a finite sum of power laws, since each term decays at the same exponential rate. The decay rate of long-block sharing on a log scale therefore identifies the dispersal rate $\sigma$ separately from the density and its recent trend.

## Depends on

- [Expected IBD block sharing under two-dimensional diffusion of ancestry](expected-ibd-block-sharing-under-spatial-diffusion.md)

## Expansion

Use $K_\nu(x) \sim \sqrt{\pi/(2x)}\, e^{-x}$ as $x \to \infty$ for fixed order $\nu$, with $x = \sqrt{2L}\, r/\sigma$. The polynomial prefactor $r^{2+\beta} x^{-1/2}$ contributes only $O(\log r)$ to the logarithm, so the exponential term dominates once $\sqrt{2L}\, r/\sigma$ exceeds about one, which for long blocks happens within a few dispersal distances. A sum of terms with different $\beta$ is dominated by the term with the largest polynomial power, and every term has the same exponential rate.

## Sources

- H. Ringbauer, G. Coop and N. H. Barton, Inferring recent demography from isolation by distance of long shared sequence blocks, *Genetics* 205 (2017), 1335–1351, <https://doi.org/10.1534/genetics.116.196220>, PMCID PMC5340342 (Equation 9 and the Discussion of the Bessel tail).
