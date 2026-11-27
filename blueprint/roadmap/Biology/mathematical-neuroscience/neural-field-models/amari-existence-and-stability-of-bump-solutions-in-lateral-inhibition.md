# Admissible bump widths in lateral-inhibition neural fields

Consider the one-dimensional neural field $\partial_t u(x, t) = -u + \int_{\mathbb{R}} w(x - y)\, H(u(y, t) - h)\, dy + s$ with Heaviside firing rate $H$, threshold $h$ and constant input $s$, where the kernel $w$ is continuous, integrable and even, with $w(0) > 0$ and exactly one positive zero $x_0$ (lateral inhibition). A bump of width $a > 0$ is a stationary solution whose excited region $\{u > h\}$ is an interval of length $a$; after a translation it is $(0, a)$. Write $W(x) = \int_0^x w$, $W_m = \max_{x > 0} W(x)$ and $W_\infty = \int_0^\infty w$. A bump with excited region $(0, a)$ exists if and only if the profile $u_a(x) = s + W(x) - W(x - a)$ satisfies the three admissibility conditions

$$
W(a) = h - s, \qquad W(x) + W(a - x) > h - s \text{ for } 0 < x < a, \qquad W(x) - W(x - a) \le h - s \text{ for } x > a,
$$

and the bump is then $u_a$ (Oleynik, Ponosov and Wyller, Theorem 2.3; since $u_a$ is symmetric about $a/2$, the last condition also covers $x < 0$). When $0 < h - s$ and $W_\infty < h - s < W_m$, the first condition has exactly two roots $a_1 < x_0 < a_2$, with $w(a_1) > 0$ and $w(a_2) < 0$; so every bump has width $a_1$ or $a_2$, and there is a bump of width $a_i$ exactly when $a_i$ satisfies the other two conditions. If $h - s > W_m$, for instance if $h - s > \int_0^\infty |w|$, there is no bump.

## Depends on

- [Necessary condition and bump profile](../amari-neural-field-bump-solutions/bump-condition-and-profile.md)
- [Amari's stability criterion for bump widths](../amari-neural-field-bump-solutions/width-stability.md)

## Expansion

1. The model: the Amari equation with Heaviside firing, the hypotheses on $w$, and the definition of a bump.
2. The shape of $W$: it increases up to the positive zero $x_0$ of $w$, where it attains $W_m$, and then decreases to $W_\infty$; hence for $\max(0, W_\infty) < h - s < W_m$ the equation $W(a) = h - s$ has exactly two positive roots $a_1 < x_0 < a_2$, with $w(a_1) > 0$ and $w(a_2) < 0$.
3. A root $a$ gives a bump exactly when it is admissible: the profile $u_a(x) = s + W(x) - W(x - a)$, which equals $h$ at $0$ and $a$, satisfies $u_a > h$ on $(0, a)$ and $u_a \le h$ outside $[0, a]$ (Oleynik, Ponosov and Wyller, Theorem 2.3).
4. Nonexistence for $h - s > W_m$: every bump of width $a$ satisfies $W(a) = h - s$ by the necessary condition, which is impossible when $h - s$ exceeds the maximum of $W$ (Gerstner, Kistler, Naud and Paninski, Section 18.3.1, equation (18.34)).
5. Amari's classification of bumps by the shape of $W$ and the value of $s$, the existence of bumps for smoothed Heaviside firing rates (Kishimoto and Amari 1979), and the existence of unstable bumps for such firing rates (Kostrykin and Oleynik), as separate statements.

## Sources

- A. Oleynik, A. Ponosov and J. Wyller, Iterative schemes for bump solutions in a neural field model, Differ. Equ. Dyn. Syst. 23 (2015), 79–98, Section 2, Theorem 2.3 (numbering of arXiv:1302.5322). <https://doi.org/10.1007/s12591-013-0191-5>
- V. Kostrykin and A. Oleynik, On the existence of unstable bumps in neural networks, Integral Equations Operator Theory 75 (2013), 445–458, Section 1. <https://doi.org/10.1007/s00020-013-2045-5>
- K. Kishimoto and S. Amari, Existence and stability of local excitations in homogeneous neural fields, J. Math. Biol. 7 (1979), 303–318. <https://doi.org/10.1007/BF00275151>
- W. Gerstner, W. M. Kistler, R. Naud and L. Paninski, *Neuronal Dynamics*, Cambridge University Press, 2014, Section 18.3.1. <https://doi.org/10.1017/CBO9781107447615>
- Original result: S. Amari, Dynamics of pattern formation in lateral-inhibition type neural fields, Biol. Cybern. 27 (1977), 77–87. <https://doi.org/10.1007/bf00337259>
