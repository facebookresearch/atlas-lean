# Debye–Smoluchowski diffusion-limited rate constant

Let molecules $B$ diffuse with relative diffusion coefficient $D > 0$ outside a fixed sphere of radius $R > 0$ in a radial potential $U$ that is continuously differentiable on $[R, \infty)$ with $U(r) \to 0$ as $r \to \infty$, at temperature $T > 0$, and suppose $\int_R^\infty e^{U(r)/k_B T} r^{-2}\, dr$ is finite; write $1/\beta$ for this integral. The radial flux toward the sphere is $J = 4\pi r^2 D\,(c' + c\, U'/k_B T)$. Consider steady states with bulk concentration $c(r) \to c_\infty > 0$ and the rate constant $k = J/c_\infty$:

- if the sphere is perfectly absorbing, $c(R) = 0$, then $k = k_D = 4\pi D\beta$ (Debye); for $U = 0$, $\beta = R$ and $k_D = 4\pi D R$ (Smoluchowski);
- if reaction at contact has total intrinsic rate constant $k_r > 0$, $J = k_r c(R)$, then $k = 4\pi D\beta\, k_r/(k_r + 4\pi D\beta\, e^{U(R)/k_B T})$; for $U = 0$ this is $4\pi D R\, k_r/(k_r + 4\pi D R)$. A surface reaction velocity $\kappa$ corresponds to $k_r = 4\pi R^2\kappa$, and $k_r = 0$ means no reaction and $k = 0$.

## Expansion

1. The model: the radial Smoluchowski equation with a potential, steady states with constant flux, and the boundary conditions at $R$ and at infinity, with the hypotheses above.
2. The substitution $c = e^{-U/k_B T}\phi$, which turns the flux into $4\pi D r^2 e^{-U/k_B T}\phi'$, and the integration from $R$ to $\infty$.
3. The absorbing and the radiation (Robin) cases as two statements, with the $U = 0$ specializations.

## Sources

- Diffusion-controlled reaction, Wikipedia, section Diffusion limit (derivation adapted from M. R. Roussel, *Foundations of Chemical Kinetics*, IOP Publishing, 2023, pp. 11-14 to 11-20). <https://en.wikipedia.org/wiki/Diffusion-controlled_reaction>
- Original result: P. Debye, Reaction rates in ionic solutions, Trans. Electrochem. Soc. 82 (1942), 265–272. <https://doi.org/10.1149/1.3071413> The rate formula follows the Wikipedia article above.
- Original result: M. von Smoluchowski, Versuch einer mathematischen Theorie der Koagulationskinetik kolloider Lösungen, Z. Phys. Chem. 92 (1918), 129–168. The rate formula follows the Wikipedia article above.
