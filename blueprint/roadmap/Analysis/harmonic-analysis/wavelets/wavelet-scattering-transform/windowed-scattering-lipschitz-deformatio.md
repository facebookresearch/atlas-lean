# Lipschitz continuity of the windowed scattering transform to deformations

Let $\psi$ be an [admissible scattering wavelet](is-admissible.md) and $J \in \mathbb{Z}$. There is $C$ such that for every real-valued $f \in L^2(\mathbb{R})$ with $\|U[P_J] f\|_1 = \sum_{m} \big(\sum_{|p| = m} \|U[p] f\|^2\big)^{1/2} < \infty$ and every $C^2$ displacement field $\tau$ with $\|\tau'\|_\infty \le 1/2$,

$$\|S_J[P_J] L_\tau f - S_J[P_J] f\| \le C\, \|U[P_J] f\|_1\, K(\tau), \qquad K(\tau) = 2^{-J}\|\tau\|_\infty + \|\tau'\|_\infty \max\Big(\log \frac{\|\Delta\tau\|_\infty}{\|\tau'\|_\infty}, 1\Big) + \|\tau''\|_\infty,$$

where $L_\tau f(x) = f(x - \tau(x))$ and $\|\Delta\tau\|_\infty = \sup_{x, u} |\tau(x) - \tau(u)|$ (S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), Theorem 2.12, equations (49)–(50), in dimension $d = 1$). For a translation $\tau = c$ the deformation terms vanish and $K(\tau) = 2^{-J}|c|$. By contrast, the Fourier modulus, which is translation invariant, satisfies no such bound: a dilation by $1 - s$ moves a frequency $\xi$ by $s\xi$, an error of order $|s|\,|\xi|\,\|f\|$ (equation (3)).

The bound is trivial when $\tau$ or $\tau''$ is unbounded, and the statement assumes both bounded so that the suprema are finite. Mallat's constant does not depend on $J$ (Lemmas 2.11 and 2.14 hold uniformly in $J$); the statement is the weaker form in which $C$ may depend on $J$.
