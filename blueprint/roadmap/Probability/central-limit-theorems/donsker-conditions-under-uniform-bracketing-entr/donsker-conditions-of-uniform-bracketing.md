# Donsker theorem under uniform bracketing entropy

**Donsker theorem under uniform bracketing entropy.** Let $(\Omega, P)$ be a probability space, $\mu$ a probability measure on a measurable space $S$, and $X_0, X_1, \dots : \Omega \to S$ mutually independent random variables, each with law $\mu$. Let $(F_i)_{i \in \iota}$ be measurable functions $S \to \mathbb{R}$ in $L^2(\mu)$ whose uniform bracketing entropy integral is finite,

$$\int_{(0,1]} \sqrt{\log N_{[\,]}(\varepsilon, F, \lVert \cdot \rVert_\infty)} \, d\varepsilon < \infty.$$

Then $F$ satisfies the Donsker conditions for $\mu$, $P$ and $X$: finite-dimensional convergence of the empirical process $\mathbb{G}_n f = n^{-1/2} \sum_{k<n} (f(X_k) - \int f \, d\mu)$ to centered Gaussian vectors with covariance given by $\mathrm{Var}_\mu$, total boundedness of $F$ in the semimetric $\rho_\mu(f, g) = \sqrt{\mathrm{Var}_\mu[f - g]}$, and asymptotic $\rho_\mu$-equicontinuity of $\mathbb{G}_n$ in outer probability.
