# Wilson-Cowan field derivatives (E population)

For the field
component `E(x, y) = (-x + (1 - rE * x) * fE (hE - wEI * y + wEE * x)) / tauE`
with gain `fE` differentiable at the E input with derivative `fE'`,
the partial derivatives are
`∂E/∂x = (-1 - rE * fE + (1 - rE * x) * fE' * wEE) / tauE` and
`∂E/∂y = ((1 - rE * x) * fE' * (-wEI)) / tauE`. The `-rE * fE` term
comes from differentiating the refractory factor `1 - rE * x`.
