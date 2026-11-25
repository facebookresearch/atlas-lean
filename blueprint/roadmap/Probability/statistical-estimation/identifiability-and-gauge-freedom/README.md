# Identifiability and gauge freedom

- [Observability in a linear flowsheet model](observability-in-a-linear-flowsheet-model.md)
- [Identifiability of a linear degradation path](identifiability-of-a-linear-degradation-path.md)
- [Nullspace ambiguity in history matching](nullspace-ambiguity-in-history-matching.md)

## Log attenuation of a single ray

Under the Beer–Lambert law a monochromatic ray of incident intensity $I_0 > 0$ transmits
$I = I_0 e^{-L}$, where $L$ is the line integral of the attenuation along the ray, so that
$L = -\log(I / I_0)$. For finitely many rays crossing finitely many attenuation cells, with design
matrix $A$ and attenuation vector $x$, the photon counts of the rays $j$ are modelled as independent
Poisson counts with means $I_{0,j} e^{-(Ax)_j}$, where $I_{0,j} \ge 0$ is the source intensity of
ray $j$. With positive source intensities, the law of the counts at $x$ determines $Ax$ and nothing
more, so the map from $x$ to this law is injective on a set of attenuation vectors exactly when
$x \mapsto Ax$ is.

- [For $I_0 > 0$, the log attenuation recovers $L$ from $I = I_0 e^{-L}$](attenuation-log-inversion.md)
- [Equal mix of line integrals $0$ and $2$: log attenuation is not $1$](mixture-log-ne-mean.md)

## Photon-count law and identification

- [Transmitted photon rate $I_{0,j} e^{-(Ax)_j}$ of a ray](transmitted-rate.md)
- [The transmitted rate as a real number is $I_{0,j} e^{-(Ax)_j}$](transmitted-rate-coe.md)
- [Attenuations with $Ax = Ay$ have the same transmitted rates](transmitted-rate-eq-of-mul-vec-eq.md)
- [With positive intensities, the transmitted rates agree iff $Ax = Ax'$](photon-rate-agree-iff.md)
- [Photon-count law: the product of Poisson laws at the transmitted rates](photon-law.md)
- [The photon-count law is the product of the rays' Poisson laws](photon-law-eq.md)
- [With positive intensities, the photon-count laws agree iff $Ax = Ax'$](photon-law-agree-iff.md)
- [For positive intensities, the count law is injective on $D$ iff $A$ is](photon-identify-iff.md)
- [If $x, x+v \in D$ with $Av = 0 \ne v$, the law is not injective on $D$](photon-not-identify-of-kernel.md)

## Finite designs from a basis

- [Linearity of the integral over a finite basis](ct-design-apply.md)
- [Radon design entry of a basis function](ct-design-entry.md)
- [The Radon transform of a finite superposition is the design sum](ct-design-radon-apply.md)

## A single ray through two cells

- [Single-ray design matrix with both entries 1 for two cells](ct-row.md)
- [Two distinct nonnegative attenuations with the same measurement](ct-nullspace-pair.md)
- [Attenuations $(1, 0)$ and $(0, 1)$ give the same transmitted rate](ct-equal-rates.md)
- [Attenuations $(1, 0)$ and $(0, 1)$ give the same photon-count law](ct-photon-law-pair.md)
- [One ray through two cells does not identify a nonnegative attenuation](ct-photon-not-identified.md)
