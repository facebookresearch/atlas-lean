# Bound for the Arakelov form in the cusp charts of a Belyi cover

This node is still to be broken down. Let $\pi \colon Y \to X(2)$ be a
[Belyi cover](belyi-cover-of-x2.md) with $Y$ of positive genus $g$, let $y$ be a cusp of $Y$ with
cusp chart $w_y \colon V_y \to B(0, 1)$, and write the
[Arakelov $(1,1)$-form](../arakelov-invariants-of-curves/arakelov-green-function.md) of $Y$ on $V_y$ as $\mu = i F_y \,
dw_y \, d\overline{w_y}$. Then $F_y$ is subharmonic on $V_y$ and

$$0 \le F_y \le \frac{128 \exp(3\pi) (\deg \pi)^4}{\pi^2 g}.$$

## Depends on

- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md)
- [Arakelov $(1,1)$-form and Arakelov–Green function](../arakelov-invariants-of-curves/arakelov-green-function.md)

## Proof depends on

- [Bound for the Arakelov form of a Belyi cover in the hyperbolic metric](jorgenson-kramer-bound.md)

The other inputs are listed under Expansion.

## Expansion

A good expansion has pages for: Lemma 3.4.2, $i \, dw_y \, d\overline{w_y} = \frac{2\pi^2
y_\kappa^2 \lvert w_y \rvert^2}{e_y^2} \mu_{\mathrm{hyp}}$ on $\dot V_y$, with $y_\kappa(\tau) =
\Im(\gamma_\kappa^{-1} \tau)$ (p. 108); the subharmonicity of $F_y$ (Jorgenson and Kramer 2004,
p. 8, and Bruin 2010, p. 58, as cited on p. 109; not read here); and the maximum principle for
subharmonic functions, which reduces the bound to $V_y \setminus V_y(2)$, where $y_\kappa^{-2} < 4$
and $\lvert w_y \rvert^{-2} \le \exp(3\pi)$ (pp. 109–110).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Lemma 3.4.2, p. 108, and Proposition 3.4.3, pp. 109–110.
