# Existence of two bump widths in lateral-inhibition neural fields

Consider the one-dimensional neural field $\partial_t u(x, t) = -u + \int_{\mathbb{R}} w(x - y)\, H(u(y, t) - h)\, dy + s$ with Heaviside firing rate $H$, threshold $h$ and constant input $s$, where the kernel $w$ is continuous, integrable and even, with $w(0) > 0$ and exactly one positive zero (lateral inhibition). A bump is a stationary solution whose excited region $\{u > h\}$ is an interval. Write $W(x) = \int_0^x w$, $W_m = \max_{x > 0} W(x)$ and $W_\infty = \int_0^\infty w$. Amari (1977) showed (as restated by Kostrykin and Oleynik) that when $0 < h - s$ and $W_\infty < h - s < W_m$, the model has bumps of two different widths $a_1 < a_2$, the smaller with $w(a_1) > 0$ and the larger with $w(a_2) < 0$. If $h - s > W_m$, for instance if $h - s > \int_0^\infty |w|$, there is no bump.

## Depends on

- [Necessary condition and bump profile](../amari-neural-field-bump-solutions/bump-condition-and-profile.md)
- [Amari's stability criterion for bump widths](../amari-neural-field-bump-solutions/width-stability.md)

## Expansion

1. The model: the Amari equation with Heaviside firing, the hypotheses on $w$, and the definition of a bump.
2. The shape of $W$: it increases up to the positive zero $x_0$ of $w$, where it attains $W_m$, and then decreases to $W_\infty$; hence for $\max(0, W_\infty) < h - s < W_m$ the equation $W(a) = h - s$ has exactly two positive roots $a_1 < x_0 < a_2$, with $w(a_1) > 0$ and $w(a_2) < 0$.
3. Each root gives a bump: the profile $u(x) = s + W(x) - W(x - a)$ satisfies $u > h$ on $(0, a)$ and $u < h$ outside $[0, a]$.
4. Nonexistence for $h - s > W_m$: every bump of width $a$ satisfies $W(a) = h - s$ by the necessary condition, which is impossible when $h - s$ exceeds the maximum of $W$ (Gerstner, Kistler, Naud and Paninski, Section 18.3.1, equation (18.34)).
5. Amari's classification of bumps by the shape of $W$ and the value of $s$, and the existence of unstable bumps for smooth firing rates, as separate statements.

## Sources

- V. Kostrykin and A. Oleynik, On the existence of unstable bumps in neural networks, Integral Equations Operator Theory 75 (2013), 445–458, Section 1. <https://doi.org/10.1007/s00020-013-2045-5>
- W. Gerstner, W. M. Kistler, R. Naud and L. Paninski, *Neuronal Dynamics*, Cambridge University Press, 2014, Section 18.3.1. <https://doi.org/10.1017/CBO9781107447615>
- Original result: S. Amari, Dynamics of pattern formation in lateral-inhibition type neural fields, Biol. Cybern. 27 (1977), 77–87. <https://doi.org/10.1007/bf00337259> The existence of two bump widths under these hypotheses, for inputs in the range stated above, follows Kostrykin and Oleynik, Section 1.
