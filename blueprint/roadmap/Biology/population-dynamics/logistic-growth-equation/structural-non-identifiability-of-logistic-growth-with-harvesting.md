# Structural non-identifiability of logistic growth with harvesting

Let $\lambda, K, d > 0$ with $\lambda \ne d$, and let $C$ solve the logistic model with a linear sink (harvesting)

$$\frac{dC}{dt} = \lambda C\Bigl(1 - \frac{C}{K}\Bigr) - d\,C, \qquad C(0) = C_0 > 0.$$

**Proposition.** With $\Lambda = \lambda - d$ and $\kappa = K\Lambda/\lambda$, the equation is the logistic equation $dC/dt = \Lambda C(1 - C/\kappa)$, so

$$C(t) = \frac{\kappa\, C_0}{C_0 + (\kappa - C_0)\, e^{-\Lambda t}}.$$

Hence the trajectory $t \mapsto C(t)$ depends on $(\lambda, d, K)$ only through $(\Lambda, \kappa)$, and for fixed $C_0$ the map $(\lambda, d, K) \mapsto C(\cdot)$ is constant on each curve $\{(\lambda, \lambda - \Lambda, \kappa\lambda/\Lambda) : \lambda > \max(0, \Lambda)\}$. The parameters $\lambda$, $d$ and $K$ are therefore not structurally identifiable from noise-free observations of $C$ on any time set, while $(\Lambda, \kappa)$ is identifiable from observations at three distinct times when $C$ is not constant. The long-time behaviour is $C(t) \to \kappa$ if $\lambda > d$ and $C(t) \to 0$ if $\lambda < d$. This corrects the source as printed after its Eq. (5), "C(t) → K as t → ∞ if λ > d": in the source's own solution (5), $e^{-\Lambda t} \to 0$ when $\Lambda = \lambda - d > 0$, so $C(t) \to \kappa C_0/C_0 = \kappa = K(\lambda - d)/\lambda$, which is less than $K$ because $d > 0$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Explicit solution of the logistic equation](logistic.md)

## Expansion

Expand $\lambda C(1 - C/K) - dC = (\lambda - d)C - (\lambda/K)C^2 = \Lambda C (1 - C\lambda/(K\Lambda))$ and apply the explicit logistic solution with rate $\Lambda$ and capacity $\kappa$. Along a curve with fixed $(\Lambda, \kappa)$, the parameters $d = \lambda - \Lambda$ and $K = \kappa\lambda/\Lambda$ vary with $\lambda$ while $C(\cdot)$ is unchanged. Under Gaussian measurement error the log-likelihood is a function of $(\Lambda, \kappa)$ only, so the univariate profile likelihoods of $d$ and $K$ are flat along these curves; Simpson and Maclaren (2024) use this model as their structurally non-identifiable case study for profile-likelihood prediction.

## Sources

- M. J. Simpson and O. J. Maclaren, "Making predictions using poorly identified mathematical models", Bulletin of Mathematical Biology (2024), <https://doi.org/10.1007/s11538-024-01294-0>, PMCID PMC11129983 (equations (3)–(5) and Section 2.2).
