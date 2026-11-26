# One Littlewood family flat in every finite positive moment

There is one family $P_N(z)=\sum_{k=0}^{N-1}\varepsilon_{N,k}z^k$, with real signs $\varepsilon_{N,k}\in\{-1,1\}$ for every $N\in\mathbb N$, such that for each real $p>0$ the normalized Haar integral over the unit circle of $\big||P_N(z)|/\sqrt N-1\big|^p$ tends to zero as $N\to\infty$. Parametrize the circle by $z=e^{2\pi i t}$ for $t\in\mathbb R/\mathbb Z$. At $N=0$ the sign family is empty and the comparator uses real division totalized at zero, which does not affect the limit. The family is chosen before $p$.

## Depends on

- [Littlewood polynomials](is-littlewood-polynomial.md).

## Proof depends on

- [Asymptotically minimal maxima](asymptotically-minimal-littlewood-maximum.md), to select a single family with a vanishing uniform upper loss.

## Proof outline

Choose signs along all lengths before choosing a moment exponent, using the linked maximum estimates and increasing thresholds. Character orthogonality gives $\int |P_N|^2=N$ for $N\geq1$. Derive convergence in measure toward 1 from this square mean and the vanishing upper loss, then use boundedness to get every finite positive moment. This is not uniform two-sided flatness.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LittlewoodFiniteFlatness.lean#L33-L36) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/076.md).
