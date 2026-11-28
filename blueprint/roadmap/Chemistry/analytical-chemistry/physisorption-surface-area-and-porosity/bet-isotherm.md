# BET isotherm

The Brunauer–Emmett–Teller (BET) isotherm models multilayer physisorption by $n/n_m = Cx/((1-x)(1-x+Cx))$ in the relative pressure $x = p/p^\circ$.

At a temperature where the adsorptive has a saturation vapour pressure $p^\circ > 0$, let $x = p/p^\circ \in [0,1)$ be
the relative pressure. The BET isotherm with specific monolayer capacity $n_m > 0$ (amount per unit adsorbent mass) and
BET constant $C > 0$ gives the specific amount adsorbed

$$
n(x) = \frac{n_m\,C\,x}{(1-x)\,(1-x+Cx)} .
$$

On $0 < x < 1$ this is equivalent to the linear BET form

$$
\frac{x}{n\,(1-x)} = \frac{1}{n_mC} + \frac{C-1}{n_mC}\,x ,
$$

so the model's BET plot is exactly linear on the whole interval. The model function is strictly increasing on $[0,1)$,
vanishes at $x = 0$ and diverges as $x \to 1^-$.

## Context

Undergraduate level. BET analysis of N2 (77 K) or Ar (87 K) isotherms is often used to report apparent surface areas of porous frameworks where a defensible BET range exists. For measured isotherms the BET plot is only approximately linear, over a selected range (often 0.05 ≤ x ≤ 0.30 for Type II and IVa isotherms); the report treats C < 2 (Type III or V isotherms) as outside the method and large C as a sign of high-energy sites or narrow micropores.

## Depends on

None.

## Proof depends on

None.

## Expansion

For $0 < x < 1$, multiplying the rational form by $(1-x)/x$ gives $n(1-x)/x = n_mC/(1 - x + Cx)$, which is positive
because $n_mC > 0$ and $1 - x + Cx > 0$; taking reciprocals gives $x/(n(1-x)) = (1 - x + Cx)/(n_mC)$, the linear form,
and the steps reverse. From a fitted line with slope $s$ and intercept $i$ one recovers $n_m = 1/(s + i)$ and
$C = 1 + s/i$ when $s + i > 0$ and $i > 0$.

## Sources

- M. Thommes, K. Kaneko, A. V. Neimark, J. P. Olivier, F. Rodriguez-Reinoso, J. Rouquerol and K. S. W. Sing, "Physisorption of gases, with special reference to the evaluation of surface area and pore size distribution (IUPAC Technical Report)", *Pure and Applied Chemistry* 87, 1051–1069 (2015), [doi.org](https://doi.org/10.1515/pac-2014-1117), Section 5.1.1, Eqn (4).
