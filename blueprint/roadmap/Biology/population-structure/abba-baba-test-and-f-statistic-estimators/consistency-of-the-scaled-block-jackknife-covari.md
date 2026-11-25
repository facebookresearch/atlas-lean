# The scaled block jackknife is consistent for independent identically distributed blocks

Let $Z_1, Z_2, \dots$ be independent, identically distributed random vectors in $\mathbb R^k$ with $\mathbb E|Z_1|^2 < \infty$, and let $V_{\mathrm{jack}, B}$ be the
[delete-one-block jackknife covariance](delete-one-block-jackknife-covariance-of-a-vecto.md) of $Z_1, \dots, Z_B$. Then

$$B\, V_{\mathrm{jack}, B} = \frac{1}{B - 1} \sum_{b=1}^B Z_b Z_b^\top - \frac{B}{B - 1}\, \bar Z_B \bar Z_B^\top \longrightarrow \operatorname{Cov}(Z_1) \quad \text{almost surely},$$

entrywise and hence in every matrix norm, by the [strong law of large numbers](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md) applied to the integrable coordinates of $Z_b$ and to the entries of $Z_b Z_b^\top$
(integrable since $|Z_{b,i} Z_{b,j}| \le |Z_b|^2$); the strong law is stated for the coordinates of the product space, and almost-sure
convergence of these averages depends only on the joint law of $(Z_b)_b$. This does
not assert consistency for dependent (linked) blocks.

## Depends on

- [Delete-one-block jackknife covariance of a mean](delete-one-block-jackknife-covariance-of-a-vecto.md)

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998). The limit is derived above.
