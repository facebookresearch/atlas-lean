# Whole-minus-sum criteria for causal emergence

**Setting.** As in [Dynamical synergy criterion for causal emergence](dynamical-synergy-criterion-for-causal-emergence.md), let $X_t = (X_t^1, \dots, X_t^n)$ be a multivariate time series (for example $n$ electrocorticography channels) and $V_t$ a supervenient feature (for example a memoryless decoder output $V_t = F(X_t)$). For lag $t' > t$ define, at order $k = 1$, the pairwise quantities

$$\Psi^{(1)}_{t,t'}(V) = I(V_t; V_{t'}) - \sum_{j=1}^{n} I(X_t^j; V_{t'}),$$

$$\Delta^{(1)}_{t,t'}(V) = \max_j \Big( I(V_t; X_{t'}^j) - \sum_{i=1}^{n} I(X_t^i; X_{t'}^j) \Big),$$

$$\Gamma^{(1)}_{t,t'}(V) = \max_j I(V_t; X_{t'}^j).$$

**Proposition.** For any PID satisfying the basic axioms:

1. $\Psi^{(k)}_{t,t'}(V) > 0$ is sufficient for $V$ to be causally emergent of order $k$;
2. $\Delta^{(k)}_{t,t'}(V) > 0$ is sufficient for $V$ to exert downward causation;
3. $\Psi^{(k)}_{t,t'}(V) > 0$ together with $\Gamma^{(k)}_{t,t'}(V) = 0$ is sufficient for causal decoupling.

The criteria use only mutual informations between pairs of variables, so for $k = 1$ they scale linearly in $n$; they can miss emergence (false negatives) because redundancy among the parts makes them more negative.

**Neural application.** With $X_t \in \mathbb{R}^{64}$ the electrocorticogram of a macaque during reaching and $V_t \in \mathbb{R}^3$ a decoded wrist position, $\Psi^{(1)} > 0$ was found for lags up to about $0.2$ s; at $t' - t = 8$ ms, $\Psi^{(1)} = 1.275 \pm 0.002$ while $\Gamma^{(1)} = 0.049 \pm 0.002$, with a time-shuffled surrogate giving significantly smaller $\Psi^{(1)}$.

## Depends on

- [Dynamical synergy criterion for causal emergence](dynamical-synergy-criterion-for-causal-emergence.md)

## Expansion

Decompose $I(V_t; V_{t'})$ with sources $(V_t, X_t)$ conditioned through supervenience: the part of the feature's self-prediction that is shared with any single part $X_t^j$ is at most $I(X_t^j; V_{t'})$, and summing over $j$ upper-bounds (indeed may double-count) all redundant and single-part unique contributions. Whatever remains when the sum is subtracted, if positive, must be unique information of $V_t$ beyond every individual part, which is causal emergence of order $1$. The same subtraction with target $X_{t'}^j$ isolates unique information about a single future part (downward causation). If additionally $V_t$ carries no information about any single future part ($\Gamma = 0$), its emergent information can only be about collective future properties, which is causal decoupling.

## Sources

- F. E. Rosas, P. A. M. Mediano, H. J. Jensen, A. K. Seth, A. B. Barrett, R. L. Carhart-Harris, D. Bor, "Reconciling emergences: An information-theoretic approach to identify causal emergence in multivariate data", *PLoS Computational Biology* 16(12) (2020) e1008289. Section "Practical criteria for large systems" (Eqs. (10a)–(10c); Proposition 1) and "Case studies" (macaque electrocorticography and motion-capture analysis, Fig. 6). <https://doi.org/10.1371/journal.pcbi.1008289>. PMCID: PMC7833221.
