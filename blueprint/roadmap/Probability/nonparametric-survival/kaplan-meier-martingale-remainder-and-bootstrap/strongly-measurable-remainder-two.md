# The discrete Kaplan–Meier remainder at time two is known at time one

Consider the two-coin censoring model. The sample space is $\Omega_0 = \{\mathrm{true}, \mathrm{false}\}^2$ with all subsets measurable; a point is $\omega = (c, d)$, where $c$ is the censoring coin and $d$ the death coin. The $\sigma$-algebra at time $1$ is $\mathcal F_1 = \sigma(c)$, the preimages of subsets of $\{\mathrm{true}, \mathrm{false}\}$ under $\omega \mapsto c$ (see the [filtration](filtration.md)). The death process, the at-risk process and the cumulative hazard are

$$N_n(c, d) = \mathbf 1\{n \ge 2,\ c = \mathrm{false},\ d = \mathrm{true}\}, \qquad Y_n(c, d) = \mathbf 1\{n = 1 \text{ or } (n = 2 \text{ and } c = \mathrm{false})\}, \qquad \alpha_n = \begin{cases} 0, & n \le 1, \\ 1/2, & n \ge 2. \end{cases}$$

The Kaplan–Meier process and the product integral of the hazard are

$$\hat S_n(\omega) = \prod_{j < n} \Bigl(1 - Y_{j+1}(\omega)^{-1}\bigl(N_{j+1}(\omega) - N_j(\omega)\bigr)\Bigr), \qquad S_n = \prod_{j < n} \bigl(1 - (\alpha_{j+1} - \alpha_j)\bigr),$$

with the convention $0^{-1} = 0$, so a step with nobody at risk contributes the factor $1$.

The vanishing-risk remainder is

$$R_n(\omega) = \sum_{k < n} \frac{\hat S_k(\omega)}{S_{k+1}}\, \mathbf 1\{Y_{k+1}(\omega) = 0\}\, (\alpha_{k+1} - \alpha_k),$$

with real division ($x/0 = 0$).

Then $R_2 : \Omega_0 \to \mathbb R$ is strongly measurable with respect to $\mathcal F_1$; for a real-valued function this is the same as $\mathcal F_1$-measurability.
