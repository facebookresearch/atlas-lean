# BET monolayer relative pressure

On the BET model isotherm with $C > 0$, the amount adsorbed equals the monolayer capacity at exactly one relative pressure, $x_m = 1/(1+\sqrt{C})$.

Let $n(x) = n_mCx/((1-x)(1-x+Cx))$ on $0 \le x < 1$ with $n_m > 0$ and $C > 0$. Then $n(x) = n_m$ holds for exactly
one $x \in [0,1)$, namely

$$
x_m = \frac{1}{1+\sqrt{C}} .
$$

In particular $x_m \in (0,1)$, $x_m = 1/2$ for $C = 1$, and $x_m$ decreases toward $0$ as $C$ grows. This is the
model-side relative pressure of monolayer completion; a measured isotherm can reach the fitted $n_m$ at a different
relative pressure, and comparing the two is an additional consistency check.

## Context

Undergraduate level. The model-side monolayer pressure is compared with the measured crossing when BET areas of microporous frameworks are screened.

## Depends on

- [BET isotherm](bet-isotherm.md)

## Proof depends on

None.

## Expansion

On $0 < x < 1$, $n(x) = n_m$ is $Cx = (1-x)^2 + Cx(1-x)$, i.e. $Cx^2 = (1-x)^2$. Since $x > 0$ and $1 - x > 0$,
taking positive square roots gives $\sqrt{C}\,x = 1 - x$, so $x = 1/(1+\sqrt{C})$; at $x = 0$ the amount is
$0 \ne n_m$.

## Sources

- M. Thommes, K. Kaneko, A. V. Neimark, J. P. Olivier, F. Rodriguez-Reinoso, J. Rouquerol and K. S. W. Sing, "Physisorption of gases, with special reference to the evaluation of surface area and pore size distribution (IUPAC Technical Report)", *Pure and Applied Chemistry* 87, 1051–1069 (2015), [doi.org](https://doi.org/10.1515/pac-2014-1117), Section 5.1.1, Eqn (4).
- E. Bell, D. Morris, M. A. Sadeghi and J. Gostick, "BEaTmap: Simplified Rigorous BET Analysis of Isothermal Adsorption Data", *Journal of Open Research Software* (2024), [doi.org](https://doi.org/10.5334/jors.403), consistency criterion 4.
