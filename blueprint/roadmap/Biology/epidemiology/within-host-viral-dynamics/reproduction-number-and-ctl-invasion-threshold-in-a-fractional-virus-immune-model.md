# Reproduction number and CTL-invasion threshold in a fractional virus–immune model

**Model.** Healthy target cells $T$, infected cells $I$, free virus $V$ and cytotoxic T lymphocytes $C$ evolve under Caputo derivatives of order $\alpha \in (0,1]$ (parameters carry the exponent $\alpha$ to keep units consistent, written here without it):

$$D^\alpha T = \lambda - \beta VT - \mu T, \quad D^\alpha I = \beta VT - kIC - \delta I, \quad D^\alpha V = N\delta I - cV, \quad D^\alpha C = qIC - \sigma C,$$

with target-cell production $\lambda$, infection rate $\beta$, death rates $\mu, \delta$, burst size $N$, viral clearance $c$, CTL killing $k$, CTL proliferation $q$ and CTL decay $\sigma$ (bilinear immune response $f_1(I,C) = qIC$).

**Proposition.** Solutions from nonnegative data exist globally, are unique and stay in $\mathbb{R}_+^4$. With

$$\mathcal{R}_0 = \frac{\beta\lambda N}{\mu c}, \qquad \varphi_0 = 1 + \frac{\sigma N\beta\delta}{q c\mu} > 1,$$

1. the infection-free equilibrium $X_0 = (\lambda/\mu, 0, 0, 0)$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$;
2. the CTL-free endemic equilibrium

$$X_1 = \Big(\frac{c}{N\beta},\ \frac{N\beta\lambda - c\mu}{N\beta\delta},\ \frac{N\beta\lambda - c\mu}{\beta c},\ 0\Big)$$

exists (is positive) iff $\mathcal{R}_0 > 1$;
3. the endemic equilibrium with an active CTL response

$$X_2 = \Big(\frac{\lambda cq}{\sigma N\beta\delta + c\mu q},\ \frac{\sigma}{q},\ \frac{N\delta\sigma}{qc},\ \frac{\delta\big[q(N\beta\lambda - c\mu) - \sigma N\beta\delta\big]}{k(\sigma N\beta\delta + c\mu q)}\Big)$$

is positive iff $\mathcal{R}_0 > \varphi_0$. Thus for $1 < \mathcal{R}_0 < \varphi_0$ the virus persists without a CTL response, and for $\mathcal{R}_0 > \varphi_0$ both $X_1$ and $X_2$ exist.

## Expansion

Equilibria of a Caputo system are the zeros of its right-hand side, so they and the thresholds coincide with the integer-order model; local stability follows from the Matignon criterion $|\arg\lambda_i| > \alpha\pi/2$, which is implied by the classical Hurwitz condition. The next-generation matrix on $(I, V)$ at $X_0$ has $F = \begin{pmatrix}0 & \beta\lambda/\mu\\ 0 & 0\end{pmatrix}$, $V = \begin{pmatrix}\delta & 0\\ -N\delta & c\end{pmatrix}$, giving $\mathcal{R}_0 = \beta\lambda N/(\mu c)$. At $X_2$ the CTL equation forces $I = \sigma/q$, the virus equation $V = N\delta I/c$, and the infected-cell balance then determines $C$, which is positive exactly when the CTL reproduction number $q I_1/\sigma = \frac{qc\mu}{\sigma N\beta\delta}(\mathcal{R}_0 - 1)$ exceeds $1$, i.e. $\mathcal{R}_0 > \varphi_0$.

## Sources

- João Paulo Simões Maurício de Carvalho, "A novel approach to understanding CoViD-19: exploring the interplay of SARS-CoV-2 and CTL response", arXiv:2103.09053 (2021), Sections 2–3 (existence and uniqueness, basic reproduction number, disease-free, CTL-free and endemic equilibria), <https://doi.org/10.48550/arXiv.2103.09053>.
