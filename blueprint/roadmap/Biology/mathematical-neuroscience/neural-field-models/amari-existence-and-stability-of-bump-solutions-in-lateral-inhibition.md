# Stationary bumps in lateral-inhibition neural fields

Consider the one-dimensional neural field $\partial_t u(x, t) = -u + \int_{\mathbb{R}} w(x - y)\, H(u(y, t) - h)\, dy + s$ with Heaviside firing rate $H$, threshold $h$ and constant input $s$, where the kernel $w$ is continuous, integrable and even, with $w(0) > 0$ and exactly one positive zero (lateral inhibition). A bump is a stationary solution whose excited region $\{u > h\}$ is an interval. Write $W(x) = \int_0^x w$, $W_m = \max_{x > 0} W(x)$ and $W_\infty = \int_0^\infty w$. Amari (1977) showed that, for inputs in a suitable range, this model has both stable and unstable bumps (as restated by Kostrykin and Oleynik): when $0 < h - s$ and $W_\infty < h - s < W_m$, there are two bump widths, the smaller with $w(a) > 0$ and the larger with $w(a) < 0$. If the excited region is an interval of length $a > 0$, the stationary equation gives $u(x) = s + \int_{x_1}^{x_1 + a} w(x - y)\, dy$, and the threshold condition at the endpoints is the self-consistency condition

$$s = h - \int_0^a w(x)\, dx$$

(Gerstner, Kistler, Naud and Paninski, Section 18.3.1, equation (18.34), with $s$ written $I^{\mathrm{ext}}$ and $h$ written $\vartheta$), that is, $W(a) = h - s$. This is a condition on the input, not a guarantee: if $h - s > W_m$, for instance if $h - s > \int_0^\infty |w|$, no width $a > 0$ satisfies it and there is no bump. When a bump of width $a$ exists (the endpoint condition holds and the profile satisfies $u > h$ inside and $u < h$ outside the interval), its width is stable if $w(a) < 0$ and unstable if $w(a) > 0$.

## Expansion

1. The model: the Amari equation with Heaviside firing, the hypotheses on $w$, and the definition of a bump.
2. The stationary profile $u(x) = s + W(x - x_1) - W(x - x_1 - a)$ with $W(x) = \int_0^x w$, the endpoint conditions $u(x_1) = u(x_1 + a) = h$, and the additional conditions $u > h$ inside and $u < h$ outside that make the profile a solution.
3. The endpoint dynamics, for an existing bump: the width obeys a scalar equation whose linearization at $a$ has the sign of $w(a)$, giving stability for $w(a) < 0$ and instability for $w(a) > 0$.
4. Amari's classification of bumps by the shape of $W$ and the value of $s$, and the existence of unstable bumps for smooth firing rates, as separate statements.

## Sources

- V. Kostrykin and A. Oleynik, On the existence of unstable bumps in neural networks, Integral Equations Operator Theory 75 (2013), 445–458, Section 1. <https://doi.org/10.1007/s00020-013-2045-5>
- W. Gerstner, W. M. Kistler, R. Naud and L. Paninski, *Neuronal Dynamics*, Cambridge University Press, 2014, Section 18.3.1. <https://doi.org/10.1017/CBO9781107447615>
- Original result: S. Amari, Dynamics of pattern formation in lateral-inhibition type neural fields, Biol. Cybern. 27 (1977), 77–87. <https://doi.org/10.1007/bf00337259> The existence of stable and unstable bumps under these hypotheses, for inputs in the range stated above, follows Kostrykin and Oleynik, Section 1.
