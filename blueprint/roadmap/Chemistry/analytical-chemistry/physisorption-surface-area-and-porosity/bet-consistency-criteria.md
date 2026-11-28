# BET consistency criteria

On a candidate approximately linear BET range, the IUPAC consistency screens require positive $n_m$ and $C$, increasing $n(1-x)$, and a measured crossing of $n_m$ inside the range.

Let an isotherm be measured at relative pressures $x_1 < \dots < x_N$ in $(0,1)$ with amounts $n_1, \dots, n_N$. Take a
candidate range $[x_a, x_b]$ whose endpoints are measured pressures and which contains several measured points, on which
the BET plot $x/(n(1-x))$ against $x$ is approximately linear, and fit the linear BET form there, giving $n_m$ and $C$.
The range passes the IUPAC consistency screens when:

1. the fit gives a finite monolayer capacity $n_m > 0$ and $C > 0$ (a negative intercept of the BET plot excludes the range);
2. $n_k(1-x_k)$ increases with $x_k$ throughout the range;
3. the measured isotherm reaches $n_m$ at a relative pressure in $[x_a, x_b]$.

In criterion 3 this page uses the following editorial convention, not prescribed by IUPAC: the measured isotherm on the
candidate range is the piecewise-linear interpolant of the measured points with $x_a \le x_k \le x_b$ only, and the
criterion holds when this interpolant takes the value $n_m$ somewhere on $[x_a, x_b]$; points outside the range are not
used and nothing is extrapolated. An optional further check compares the in-range crossing with the model-side value
$1/(1+\sqrt{C})$ within a chosen tolerance; it is applied only when the interpolant takes the value $n_m$ at exactly
one point of $[x_a, x_b]$, and otherwise the range is reported as ambiguous for that check. Passing these screens does
not make a range linear or valid for a linear fit; they can admit several ranges, do not validate $n_m$ as a true
monolayer capacity, and for Type I isotherms the resulting area remains apparent.

## Context

Graduate level. These consistency criteria are the IUPAC-recommended procedure for BET areas of MOFs and zeolites; software such as BEaTmap applies them together with fit-quality and point-count criteria to every candidate range.

## Depends on

- [BET isotherm](bet-isotherm.md)
- [BET monolayer relative pressure](bet-monolayer-relative-pressure.md)

## Proof depends on

None.

## Expansion

Criteria 1–3 are the report's; the in-range interpolation and uniqueness rules make criterion 3 and the optional
comparison single-valued. The monolayer relative pressure of the BET model is used only by the optional comparison.

## Sources

- M. Thommes, K. Kaneko, A. V. Neimark, J. P. Olivier, F. Rodriguez-Reinoso, J. Rouquerol and K. S. W. Sing, "Physisorption of gases, with special reference to the evaluation of surface area and pore size distribution (IUPAC Technical Report)", *Pure and Applied Chemistry* 87, 1051–1069 (2015), [doi.org](https://doi.org/10.1515/pac-2014-1117), Section 5.2.2, criteria 1–3.
- E. Bell, D. Morris, M. A. Sadeghi and J. Gostick, "BEaTmap: Simplified Rigorous BET Analysis of Isothermal Adsorption Data", *Journal of Open Research Software* (2024), [doi.org](https://doi.org/10.5334/jors.403), consistency criteria 3 and 4, and practical criteria 5 and 6.
