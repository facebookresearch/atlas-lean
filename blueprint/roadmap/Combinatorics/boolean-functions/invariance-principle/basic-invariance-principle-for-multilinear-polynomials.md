# Basic invariance principle for low-degree multilinear polynomials

Let $Q$ be a formal multilinear polynomial of degree at most $k$, and let $\mathbf{X}$ and $\mathbf{Y}$ be vectors of independent random variables, each satisfying the invariance hypothesis. For every $C^4$ function $\psi : \mathbb{R} \to \mathbb{R}$ with $|\psi''''| \le C$,

$$\big|\mathbb{E}\,\psi(Q(\mathbf{X})) - \mathbb{E}\,\psi(Q(\mathbf{Y}))\big| \le \frac{C}{12}\, 9^k \sum_i \mathrm{Inf}_i[Q]^2 .$$

If moreover $\mathrm{Var}[Q] \le 1$ and all influences are at most $\varepsilon$, the right side is at most $\frac{C}{12}k\,9^k\varepsilon$, and the Lévy distance between $Q(\mathbf{X})$ and $Q(\mathbf{Y})$ is at most $c\, 2^k \varepsilon^{1/5}$ for a universal constant $c$. In particular for $f : \{-1,1\}^n \to \mathbb{R}$ of degree at most $k$, $\mathrm{Var}[f] \le 1$ and all influences at most $\varepsilon$, the distribution of $f$ on uniform bits is within Lévy distance $c\, 2^k\varepsilon^{1/5}$ of the distribution of its Fourier polynomial evaluated at independent standard Gaussians.

## Proof sketch

Replace the variables one at a time (Lindeberg). At step $t$ write $Q = E_tQ + z_t D_tQ$ with $E_tQ, D_tQ$ free of $z_t$; a third-order Taylor expansion of $\psi$ around the part free of $z_t$ cancels the first three moments, leaving an error at most $\frac{C}{24}\big(\mathbb{E}[L^4] + \mathbb{E}[L'^4]\big)$, where $L, L'$ are $z_tD_tQ$ evaluated at the mixed inputs $(y_1, \dots, y_{t-1}, x_t, \dots, x_n)$ and $(y_1, \dots, y_t, x_{t+1}, \dots, x_n)$. Each fourth moment is at most $9^k\,\mathrm{Inf}_t[Q]^2$ by the Bonami bound for independent mixed inputs with mean $0$, variance $1$, third moment $0$ and fourth moment at most $9$ (O'Donnell, Cor. 9.6): for a multilinear $P = R + zS$ of degree at most $k$ with $R, S$ free of the independent $z$, the odd moments of $z$ vanish and $\mathbb{E}[P^4] = \mathbb{E}R^4 + 6\,\mathbb{E}[R^2S^2] + \mathbb{E}z^4\,\mathbb{E}S^4 \le 9^k(\mathbb{E}R^2)^2 + 2\cdot 9^k\,\mathbb{E}R^2\,\mathbb{E}S^2 + 9^k(\mathbb{E}S^2)^2 = 9^k(\mathbb{E}P^2)^2$ by induction on the number of variables and Cauchy–Schwarz. Summing over $t$ gives the $C^4$ bound, and $\sum_t\mathrm{Inf}_t[Q]^2 \le \varepsilon\sum_t\mathrm{Inf}_t[Q] \le \varepsilon k\,\mathrm{Var}[Q]$. Smoothing a step function at scale $\eta$ with $|\psi''''| = O(\eta^{-4})$ and optimizing $\eta$ gives the Lévy bound (O'Donnell, (11.29), Cor. 11.67 and Cor. 11.70).

## Depends on

- [Lévy distance and the hypothesis of the basic invariance principle](levy-distance-and-invariance-hypothesis.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Invariance principle for sums of independent random variables](invariance-principle-for-sums.md)
- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
