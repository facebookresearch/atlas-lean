# Quadratic calibration on dimensioned quantities

Let $d$ be a dimension over the seven ISQ base quantities and $\mathcal{V}$ the
[voltage dimension](voltage-dim.md). For coefficients $c_0$, $c_1$ and $c_2$ of dimensions $d$,
$d\,\mathcal{V}^{-1}$ and $d\,\mathcal{V}^{-2}$ and a voltage $v$ of dimension $\mathcal{V}$, the
calibrated output is the quantity of dimension $d$

$$
f(v) = c_0 + c_1 v + c_2 v^2,
$$

where the products $c_1 v$ and $c_2 (v v)$, of dimensions $d\,\mathcal{V}^{-1}\mathcal{V}$ and
$d\,\mathcal{V}^{-2}\mathcal{V}^2$, are recast to dimension $d$ by the identities
$d\,\mathcal{V}^{-1}\mathcal{V} = d$ and $d\,\mathcal{V}^{-2}\mathcal{V}^2 = d$ before the three
terms are added. Its coordinate is the [real quadratic calibration](quad-calibration.md) of the
coordinates ([coordinate of the dimensioned calibration](quad-calibration-qty-val.md)).
