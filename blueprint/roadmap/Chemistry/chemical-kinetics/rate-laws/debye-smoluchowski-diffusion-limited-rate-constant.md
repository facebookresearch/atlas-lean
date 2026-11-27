# Collins–Kimball rate constant for a partially absorbing sphere

Let molecules $B$ diffuse with relative diffusion coefficient $D > 0$ outside a fixed sphere of radius $R > 0$ in a radial potential $U$ that is continuously differentiable on $[R, \infty)$ with $U(r) \to 0$ as $r \to \infty$, at thermal energy $k_BT > 0$, and suppose $\int_R^\infty e^{U(r)/k_B T} r^{-2}\, dr$ is finite, with value [$1/\beta$](../../../Biology/not-yet-classified/diffusion-limited-rate/inv-beta.md). Consider a [steady radial profile](../../../Biology/not-yet-classified/diffusion-limited-rate/is-steady-profile.md) $c$ with current $J$, $4\pi r^2 D\,(c' + c\, U'/k_BT) = J$ for $r \ge R$, with bulk concentration $c(r) \to c_\infty > 0$, and suppose reaction at contact has total intrinsic rate constant $k_r > 0$, so that $J = k_r c(R)$ (the radiation boundary condition of Collins and Kimball 1949). Then the rate constant $k = J/c_\infty$ is

$$k = \frac{4\pi D\beta\, k_r}{k_r + 4\pi D\beta\, e^{U(R)/k_B T}},$$

which for $U = 0$ is $4\pi D R\, k_r/(k_r + 4\pi D R)$ (Collins and Kimball 1949; with a potential, Roussel 2023, Section 11.4.1). A surface reaction velocity $\kappa$ corresponds to $k_r = 4\pi R^2\kappa$. As $k_r \to \infty$ the rate constant tends to $4\pi D\beta$, the rate constant of the perfectly absorbing sphere $c(R) = 0$ given by the [steady radial current with an interaction potential](../../../Biology/not-yet-classified/diffusion-limited-rate/current-eq.md) (Debye 1942), and for $U = 0$ to $4\pi D R$, [Smoluchowski's steady radial current](../../../Biology/not-yet-classified/diffusion-limited-rate/current-eq-smoluchowski.md).

## Depends on

- [Is Steady Profile](../../../Biology/not-yet-classified/diffusion-limited-rate/is-steady-profile.md)
- [Inv Beta](../../../Biology/not-yet-classified/diffusion-limited-rate/inv-beta.md)

## Expansion

1. The model: the radial Smoluchowski equation with a potential, steady states with constant flux, and the radiation boundary condition $J = k_r c(R)$ at $R$ with the bulk condition at infinity, with the hypotheses above.
2. The substitution $c = e^{-U/k_B T}\phi$, which turns the flux into $4\pi D r^2 e^{-U/k_B T}\phi'$, and the integration from $R$ to $\infty$.
3. Solving the radiation (Robin) condition for $J$, and the $U = 0$ specialization.

## Sources

- P. Debye, Reaction rates in ionic solutions, Trans. Electrochem. Soc. 82 (1942), 265–272, Eq. (5). <https://doi.org/10.1149/1.3071413>
- M. von Smoluchowski, Versuch einer mathematischen Theorie der Koagulationskinetik kolloider Lösungen, Z. Phys. Chem. 92 (1917), 129–168.
- Original result: F. C. Collins and G. E. Kimball, Diffusion-controlled reaction rates, J. Colloid Sci. 4 (1949), 425–437.
- M. R. Roussel, *Foundations of Chemical Kinetics*, IOP Publishing, 2023, Section 11.4.1, pp. 11-14 to 11-20. <https://doi.org/10.1088/978-0-7503-5321-2>
