# Power-law and Weibull release fits (empirical)

The power law $M_t/M_\infty = kt^n$ and the Weibull function $1 - e^{-\alpha t^\beta}$ are empirical fits to release curves; a fitted exponent over a finite window is not identified with any exact solution's behaviour.

Empirical models. The Ritger–Peppas (Korsmeyer–Peppas) power law, with $k, n > 0$ and $kt^n$ dimensionless,

$$\frac{M_t}{M_\infty} = k\,t^{n},$$

is fitted to release data over a finite window, usually up to about 60% release. Readings reported in the sources: $n = 0.5$ for Fickian diffusion (Case I) and $n = 1$ for Case II transport or release dominated by surface erosion, intermediate values being called anomalous; a two-term form $k_1\sqrt t + k_2 t$ separates diffusion and relaxation contributions heuristically. The Weibull function, with $\alpha, \beta > 0$,

$$\frac{m(t)}{m_\infty} = 1 - e^{-\alpha t^{\beta}},$$

generalizes first-order dissolution by replacing $t$ with $t^\beta$; for small $\alpha t^\beta$ it behaves as $\alpha t^\beta$. In one cited dataset $\beta \le 0.75$ was associated with Fickian diffusion.

## Context

Undergraduate, with a methodological warning: these are fits, not theorems, and a good fit does not identify a mechanism. The reading $n = 0.5$ refers to Fickian diffusion, whose exact solutions in simple geometries are on pages such as [Fickian release from a slab](fickian-release-from-a-slab.md); their short-time behaviour is a separate result (Expansion), and a fitted exponent is not the same object. Geometry-dependent best-fit exponents over a 60% window depend on the window, the norm and weighting, and the geometry; the values reported by Ritger and Peppas were not verified here because only a truncated abstract was accessible. The power law exceeds 1 at large $t$. Li and Mooney instead summarize hydrogel systems by the 24 h release fraction and the half-life $t_{1/2}$, a descriptive chart.

## Depends on

The following is a conceptual prerequisite (an exact model behind the $n = 0.5$ reading), not a proof of the fit:

- [Fickian release from a slab into a perfect sink](fickian-release-from-a-slab.md)

## Proof depends on

None.

## Expansion

To connect fits to theorems: state and prove the short-time asymptotics of the exact Fickian solutions for the slab, cylinder and sphere, and quantify the best single power law over $0 \le M_t/M_\infty \le 0.6$ under a stated norm, which yields geometry-dependent exponents as derived quantities; state the surface-eroding slab as the exact $n = 1$ case. Inference of mechanism from fitted $n$ for swelling or degrading gels remains empirical.

## Sources

- J. Li and D. J. Mooney, "Designing hydrogels for controlled drug delivery", Nature Reviews Materials 1, 16071 (2016), <https://doi.org/10.1038/natrevmats.2016.71>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC5898614/>: section "Release kinetics of hydrogel systems": Eq. (2), the reading of $n$, and Figure 5 (release property chart with 24 h fraction and $t_{1/2}$)
- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 3.2.2, Eqs. (40)–(41) and the remark on the first 60% of release; Section 4.2, Eqs. (70)–(75) (Noyes–Whitney extension, Weibull function, linearization, dataset-specific $\beta$ thresholds, small-time reduction to the power law)
- P. L. Ritger and N. A. Peppas, "A simple equation for description of solute release I. Fickian and non-fickian release from non-swellable devices in the form of slabs, spheres, cylinders or discs", Journal of Controlled Release 5, 23–36 (1987), <https://doi.org/10.1016/0168-3659(87)90034-4>; only a truncated abstract was read: abstract: introduction of $M_t/M_\infty = kt^n$ with $n$ characteristic of the release mechanism; the rest of the abstract and the paper were not accessible
