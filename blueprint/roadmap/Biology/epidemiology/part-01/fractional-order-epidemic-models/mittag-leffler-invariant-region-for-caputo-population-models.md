# Mittag-Leffler invariant region for Caputo population models

Let $0<\alpha\le 1$, $\Lambda\ge 0$, $\delta>0$, and let $N(t)\ge 0$ be the total population of a Caputo compartmental model with constant recruitment $\Lambda$ and per-capita removal at least $\delta$ from every compartment, so that

$$
{}^{C}D_t^{\alpha}N(t)+\delta N(t)\le \Lambda,\qquad t>0 .
$$

Then, with the two-parameter Mittag-Leffler function $E_{\alpha,\beta}(z)=\sum_{n\ge 0} z^n/\Gamma(\alpha n+\beta)$ and $E_\alpha=E_{\alpha,1}$,

$$
N(t)\le N(0)\,E_{\alpha}(-\delta t^{\alpha})+\Lambda\,t^{\alpha}E_{\alpha,\alpha+1}(-\delta t^{\alpha})
= N(0)\,E_{\alpha}(-\delta t^{\alpha})+\frac{\Lambda}{\delta}\big(1-E_{\alpha}(-\delta t^{\alpha})\big).
$$

Since $0<E_\alpha(-\delta t^\alpha)\le 1$ is decreasing to $0$, it follows that

1. the region $\Omega=\{x\in\mathbb{R}^n_{+}: N\le \Lambda/\delta\}$ is positively invariant, and
2. $\limsup_{t\to\infty}N(t)\le \Lambda/\delta$ for every nonnegative initial condition, so $\Omega$ attracts all nonnegative solutions.

This is the fractional analogue of the integer-order bound $N(t)\le N(0)e^{-\delta t}+\frac{\Lambda}{\delta}(1-e^{-\delta t})$, which it recovers at $\alpha=1$ because $E_1(z)=e^{z}$; the decay toward the bound is algebraic, $E_\alpha(-\delta t^\alpha)\sim t^{-\alpha}/(\delta\,\Gamma(1-\alpha))$ for $\alpha<1$, rather than exponential.

## Depends on

- [Well-posedness of Caputo fractional initial value problems](caputo-fractional-initial-value-problem-well-posedness.md)

## Expansion

Taking Laplace transforms, ${}^{C}D_t^{\alpha}N$ transforms to $s^{\alpha}\hat N(s)-s^{\alpha-1}N(0)$, so the equality case gives $\hat N(s)=\frac{\Lambda}{s(s^{\alpha}+\delta)}+\frac{s^{\alpha-1}N(0)}{s^{\alpha}+\delta}$. The transform pair $\mathcal{L}[t^{\beta-1}E_{\alpha,\beta}(-\delta t^{\alpha})]=s^{\alpha-\beta}/(s^{\alpha}+\delta)$ with $\beta=1$ and $\beta=\alpha+1$ inverts this, and the fractional comparison principle turns the differential inequality into the stated bound. The second form uses the identity $z\,E_{\alpha,\alpha+1}(z)=E_\alpha(z)-1$ at $z=-\delta t^\alpha$. The source states the bound with the argument printed as $\delta t^{\alpha}$; the Laplace computation it gives, with denominator $s^{\alpha}+\delta$, yields $-\delta t^{\alpha}$ as above.

## Sources

- M. A. Aba Oud, A. Ali, H. Alrabaiah, S. Ullah, M. A. Khan, S. Islam, "A fractional order mathematical model for COVID-19 dynamics with quarantine, isolation, and environmental viral load", *Advances in Difference Equations* 2021 (2021) 106. <https://doi.org/10.1186/s13662-021-03265-4>. PMCID: PMC7877321. (Lemma 1.)
