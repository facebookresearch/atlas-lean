# Bubble criterion for Wolbachia invasion and release-size thresholds

**Setting.** The infection frequency $p(t,x) \in [0,1]$, $x \in \mathbb R^d$, satisfies

$$ \partial_t p - \sigma\Delta p = f(p), $$

with $\sigma > 0$ and a bistable $f$: there is $\theta \in (0,1)$ with $f(0) = f(\theta) = f(1) = 0$, $f < 0$ on $(0,\theta)$, $f > 0$ on $(\theta, 1)$ and $\int_0^1 f > 0$. (For *Wolbachia* with fecundity cost $s_f$, cytoplasmic-incompatibility strength $s_h$, death-rate ratio $\delta$ and perfect maternal transmission, $f(p) = \delta d_s p\,\frac{-s_hp^2 + (1 + s_h - (1-s_f)/\delta)p + (1-s_f)/\delta - 1}{s_hp^2 - (s_f + s_h)p + 1}$.) Let $F(x) = \int_0^x f$ and let $\theta_c \in (0,1)$ be the unique zero of $F$ in $(0,1)$.

**Theorem (bubble criterion).** For every $\alpha \in (\theta_c, 1]$ there is a compactly supported, radially non-increasing function $v_\alpha$ with $v_\alpha(0) = \alpha$ (the *$\alpha$-bubble*) such that every solution with $p(0,\cdot) \ge v_\alpha(|\cdot|)$ satisfies $p(t,\cdot) \to 1$ locally uniformly. The support can be taken to be the ball of radius

$$ R_\alpha = \sqrt\sigma\,\inf_{\rho\in\Gamma}\sqrt{\frac{1-\rho^d}{(1-\rho)^2}\cdot\frac{1}{\int_0^\alpha\big(1 - \frac{1-\rho}{\alpha}x\big)^d f(x)\,dx}}, \qquad \Gamma = \Big\{\rho \in (0,1) : \int_0^\alpha\big(1 - \tfrac{1-\rho}{\alpha}x\big)^d f(x)\,dx > 0\Big\}, $$

and in dimension one sharply $\mathrm{supp}\,v_\alpha = [-L_\alpha, L_\alpha]$ with

$$ L_\alpha = \sqrt{\frac\sigma2}\int_0^\alpha\frac{dv}{\sqrt{F(\alpha) - F(v)}}. $$

Conversely, in dimension one, if $p(0,\cdot) < \theta$ everywhere or $p(0,\cdot) < v_{\theta_c}(\cdot - \zeta)$ for some $\zeta$ (the ground state), then $p \to 0$ uniformly.

**Release thresholds.** Suppose a resident population of uniform density $N_0$ receives released infected mosquitoes with density $X(x)$, so $p(0,x) = X(x)/(X(x) + N_0)$. In dimension one, for a single release of $N$ mosquitoes with Gaussian profile $N(2\pi\sigma)^{-1/2}e^{-x^2/(2\sigma)}$ there is a constant $C > 0$ (depending only on $f$) such that the profile lies above some $\alpha$-bubble iff

$$ N \ge C\, N_0\sqrt{2\pi\sigma}. $$

In any dimension, if $\alpha \in (\theta_c, 1)$ and each of $k$ releases has size at least $N^* = (2\pi\sigma)^{d/2}\frac{\alpha}{1-\alpha}N_0$, with release points placed at random in a compact set containing a ball of radius $R_\alpha$, the probability that the resulting profile dominates a bubble tends to $1$ as $k \to \infty$.

## Expansion

The bubble is a compactly supported subsolution of the stationary problem $-\sigma\Delta v = f(v)$; a solution started above a subsolution increases in time and, by bistability and $F(1) > 0$, converges to $1$. The radius $R_\alpha$ comes from an explicit family of radially decreasing test profiles indexed by $\rho \in \Gamma$, for which the subsolution condition reduces to positivity of $\int_0^\alpha(1 - \frac{1-\rho}{\alpha}x)^d f(x)\,dx$; optimizing the resulting support radius over $\rho$ gives the formula; in one dimension the phase-plane first integral $\frac\sigma2 (v')^2 = F(\alpha) - F(v)$ of the stationary equation gives the exact half-width $L_\alpha$, which is finite precisely when $F(\alpha) > 0$, i.e. $\alpha > \theta_c$. The ground state $v_{\theta_c}$ separates extinction from invasion (sharp threshold results of Du–Matano and Muratov–Zhong). For a Gaussian release, domination of a bubble is equivalent to a pointwise inequality between $\log\big(N/(N_0\sqrt{2\pi\sigma})\big)$ and an explicit function of the frequency level, whose worst case gives the constant $C$; the multi-release result is a coupon-collector argument on the random release positions.

## Sources

- Martin Strugarek, Nicolas Vauchelet, Jorge P. Zubelli, "Quantifying the survival uncertainty of Wolbachia-infected mosquitoes in a spatial model", arXiv:1608.06792 (2016), Section 2.1 (bistability hypothesis, Theorem 1 with the radii $R_\alpha$ and $L_\alpha$, Proposition 1), Section 2.3 (Proposition 2, Corollary 1), Section 3 (Propositions 3–4), Section 4.1 (Proposition 5, Lemmas 2–3). <https://doi.org/10.48550/arXiv.1608.06792>. Published version: Mathematical Biosciences & Engineering 15(4) (2018), 961–991, <https://doi.org/10.3934/mbe.2018043>; locators above refer to the arXiv version.
