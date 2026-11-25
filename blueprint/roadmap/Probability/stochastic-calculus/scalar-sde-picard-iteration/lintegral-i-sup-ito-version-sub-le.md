# Maximal difference estimate for Lipschitz Itô versions

Let $B$ have real Brownian finite-dimensional laws, be adapted to $(\mathcal F_t)$, and have increments independent of the past filtration. Let $X,Y$ be progressive real processes. Fix $t\ge0$ and suppose both input energies $\mathbb E\int_0^t|X_s|^2\,ds$ and $\mathbb E\int_0^t|Y_s|^2\,ds$ are finite. Let $\sigma$ be globally Lipschitz with constant $K\ge0$.

Suppose $J,L$ are martingales for this filtration, continuous on every sample path, with fixed-time almost-sure equalities to the actual Itô integrals of $\sigma(X)$ and $\sigma(Y)$ respectively, at every nonnegative time. Then

$$\mathbb E\sup_{0\le s\le t}|J_s-L_s|^2
\le4K^2\,\mathbb E\int_0^t|X_s-Y_s|^2\,ds.$$

All moments in this statement are nonnegative extended integrals. Brownian finite-dimensional laws imply probability normalization. No completeness or right continuity of the filtration, or continuity of the driving paths, is needed. The inputs themselves need not have continuous paths.

Apply Doob's $L^2$ inequality to the difference of the two continuous martingales. Fixed-time equality transfers its terminal second moment to the actual Itô difference, where Lipschitz composition and the difference isometry apply. No pathwise linearity of version selection is assumed.
