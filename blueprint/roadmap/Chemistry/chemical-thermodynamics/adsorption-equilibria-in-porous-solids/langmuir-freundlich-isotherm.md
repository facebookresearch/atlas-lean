# Langmuir–Freundlich isotherm

The Langmuir–Freundlich isotherm $n = a\,b\,p^c/(1+b\,p^c)$ adds a heterogeneity exponent $c$ to the Langmuir law.

For pressure $p \ge 0$ the Langmuir–Freundlich loading is

$$
n(p) = \frac{a\,b\,p^{c}}{1 + b\,p^{c}},
$$

with maximal loading $a > 0$, affinity constant $b > 0$ in units of $\mathrm{kPa}^{-c}$ (so that $b\,p^c$ is
dimensionless) and heterogeneity exponent $c > 0$. For $c = 1$ it is the Langmuir isotherm. The function is strictly
increasing on $p \ge 0$ and tends to $a$ as $p \to \infty$. For $c < 1$ its slope at $p = 0^+$ is infinite and for
$c > 1$ it is zero, so it has a finite nonzero Henry constant only when $c = 1$. The literature also writes the term as
$(bp)^c$, in which case $b$ has units $\mathrm{kPa}^{-1}$.

## Context

Graduate level. The (dual-site) Langmuir–Freundlich fit is the usual smooth interpolant of measured CO2 isotherms of metal–organic frameworks before isosteric enthalpies are extracted.

## Depends on

- [Langmuir isotherm](langmuir-isotherm.md)

## Proof depends on

None.

## Expansion

The low-pressure behaviour follows from $n(p) \sim a\,b\,p^c$ as $p \to 0^+$. Because the slope at zero is not
finite and nonzero when $c \ne 1$, the model is not thermodynamically consistent at low coverage and is unsuitable as
input to ideal adsorbed solution theory.

## Sources

- A. Nuhnen and C. Janiak, "A practical guide to calculate the isosteric heat/enthalpy of adsorption via adsorption isotherms in metal–organic frameworks, MOFs", *Dalton Transactions* 49, 10295–10307 (2020), [doi.org](https://doi.org/10.1039/d0dt01784a), Eqn (4) and the remark on the form $(b\,p)^c$.
- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/), FAQ "Why don't you include the commonly-used Freundlich or Langmuir-Freundlich isotherms?".
