# Viral-load threshold in the fuzzy SIR model with vaccination and treatment

**Model.** Let $S, I, R \ge 0$ be population proportions and let $\Omega \ge 0$ denote the viral load of an infective. Fix a birth/death rate $\mu > 0$, vaccine effectiveness $\tau \in [0,1)$, adherence to health protocols $\pi \in [0,1)$ and treatment effectiveness $\theta \in [0,1]$, and put $c = (1-\tau)(1-\pi) > 0$. Transmission $\beta(\Omega) \ge 0$, recovery $\gamma(\Omega) \ge 0$ and disease-induced death $\mu_C(\Omega) \ge 0$ are functions of $\Omega$ (fuzzy membership functions), and

$$\begin{aligned}
\dot S &= \mu - c\,\beta(\Omega) S I - (\mu+\tau+\pi) S,\\
\dot I &= c\,\beta(\Omega) S I - \big(\mu + \mu_C(\Omega) + \theta + \gamma(\Omega)\big) I,\\
\dot R &= \big(\theta + \gamma(\Omega)\big) I + (\pi+\tau) S - \mu R.
\end{aligned}$$

In the source the membership functions are piecewise linear: $\beta$ is $0$ for $\Omega \le \Omega_{\min}$, rises linearly on $(\Omega_{\min},\Omega_0)$ and is constant on $[\Omega_0,\Omega_{\max})$; $\mu_C$ increases linearly from a floor $\mu_0^C$ on $[0,\Omega_0)$ and is constant afterwards; $\gamma$ decreases linearly from $1$ to a floor on $[0,\Omega_0)$ and is constant afterwards, with treatment $\theta$ flattening the slopes of $\mu_C$ and $\gamma$.

Write $K(\Omega) = \theta + \mu_C(\Omega) + \gamma(\Omega) + \mu$. For each fixed $\Omega$:

1. The disease-free equilibrium is $E_0 = \left(\frac{\mu}{\pi+\tau+\mu},\, 0,\, \frac{\pi+\tau}{\pi+\tau+\mu}\right)$ and the next-generation reproduction number is

    $$\mathfrak{R}_0(\Omega) = \frac{c\,\beta(\Omega)\,\mu}{(\pi+\tau+\mu)\,K(\Omega)}.$$

2. $E_0$ is locally asymptotically stable if $\mathfrak{R}_0(\Omega) < 1$ and unstable if $\mathfrak{R}_0(\Omega) > 1$.
3. If $\mathfrak{R}_0(\Omega) > 1$ there is a unique endemic equilibrium with

    $$S^* = \frac{K(\Omega)}{c\,\beta(\Omega)}, \qquad I^* = \frac{(\pi+\tau+\mu)\big(\mathfrak{R}_0(\Omega) - 1\big)}{c\,\beta(\Omega)}, \qquad R^* = \frac{(\theta+\gamma(\Omega)) I^* + (\pi+\tau) S^*}{\mu},$$

    and it is locally asymptotically stable.

4. (Viral-load threshold.) If, on an interval of viral loads, $\Omega \mapsto \mathfrak{R}_0(\Omega)$ is continuous and strictly increasing and crosses $1$ at $\Omega^*$, i.e. $c\,\beta(\Omega^*)\,\mu = (\pi+\tau+\mu) K(\Omega^*)$, then on that interval the disease-free equilibrium is locally asymptotically stable for $\Omega < \Omega^*$ and the endemic equilibrium is locally asymptotically stable for $\Omega > \Omega^*$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At $E_0$ the Jacobian is block triangular with eigenvalues $-(\pi+\tau+\mu)$, $-\mu$ and $\lambda_3 = K(\Omega)\big(\mathfrak{R}_0(\Omega) - 1\big)$, which gives item 2. At the endemic point $c\beta S^* = K$, so the $(I,I)$ entry of the Jacobian vanishes and the $(S,I)$ block has trace $-(\pi+\tau+\mu)\mathfrak{R}_0$ and determinant $(\pi+\tau+\mu) K (\mathfrak{R}_0 - 1)$; by Routh–Hurwitz both eigenvalues have negative real part when $\mathfrak{R}_0 > 1$, and the third eigenvalue is $-\mu$. Item 4 is the transcritical exchange of stability at $\mathfrak{R}_0 = 1$ read along the viral-load axis; with the piecewise-linear membership functions the threshold $\Omega^*$ lies in $(\Omega_{\min}, \Omega_0]$ and has a closed form. The monotonicity hypothesis is needed because $\mu_C$ increases while $\gamma$ decreases in $\Omega$, so $K(\Omega)$ need not be monotone. Raising $\tau$, $\pi$ or $\theta$ lowers $\mathfrak{R}_0$ and pushes $\Omega^*$ up, which is how vaccination, protocol adherence and treatment act in this model.

## Sources

- Muhammad Abdy, Syafruddin Side, Suwardi Annas, Wahyuddin Nur, Wahidah Sanusi, "An SIR epidemic model for COVID-19 spread with fuzzy parameter: the case of Indonesia", *Advances in Difference Equations* (2021), Equations (4)–(9) and (13)–(21), Section "Stability analysis" (Theorems 1 and 2 and the Corollary). <https://doi.org/10.1186/s13662-021-03263-6>. PMCID: PMC7877290.
