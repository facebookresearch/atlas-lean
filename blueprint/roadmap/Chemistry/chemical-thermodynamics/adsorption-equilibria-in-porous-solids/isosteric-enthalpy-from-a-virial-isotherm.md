# Isosteric enthalpy from a virial isotherm

If $\ln p = \ln n + T^{-1}\sum_i a_in^i + \sum_j b_jn^j$ at every temperature, the isosteric enthalpy is $R\sum_i a_in^i$.

Let the equilibrium pressure $p > 0$ at loading $n > 0$ and temperature $T > 0$, both in fixed units, satisfy the
virial-type equation

$$
\ln p = \ln n + \frac{1}{T}\sum_{i=0}^{m} a_i n^i + \sum_{j=0}^{m'} b_j n^j
$$

with temperature-independent coefficients $a_i$ (units K per $n^i$) and $b_j$. Then the isosteric enthalpy of
adsorption is

$$
\Delta H_{ads}(n) = R\sum_{i=0}^{m} a_i n^i, \qquad Q_{st}(n) = -R\sum_{i=0}^{m} a_i n^i,
$$

independent of temperature. As $n \to 0^+$ the model polynomial tends to $R\,a_0$; this is an extrapolation of the
fitted model, not a measured value, and the source shows that fits with different lower loading bounds can give very
different $a_0$. The sign of $\Delta H_{ads}(n)$ at a given loading is that of the whole sum, not of $a_0$ alone.

## Context

Graduate level. Virial analysis is the common route to coverage-dependent isosteric heats of CO2, SO2 and H2 in metal–organic frameworks; in the source the coefficients are fitted simultaneously to isotherms at two or more temperatures over the measured loading range.

## Depends on

- [Isosteric enthalpy of adsorption](isosteric-enthalpy-of-adsorption.md)

## Proof depends on

None.

## Expansion

At fixed $n$ the right side is affine in $1/T$ with slope $\sum_i a_in^i$, so
$(\partial\ln p/\partial(1/T))_n = \sum_i a_in^i$; multiplying by $R$ gives the result.

## Sources

- A. Nuhnen and C. Janiak, "A practical guide to calculate the isosteric heat/enthalpy of adsorption via adsorption isotherms in metal–organic frameworks, MOFs", *Dalton Transactions* 49, 10295–10307 (2020), [doi.org](https://doi.org/10.1039/d0dt01784a), Eqns (2), (3), (7), (8) and (9), and the discussion of fits with additional low-uptake points.
