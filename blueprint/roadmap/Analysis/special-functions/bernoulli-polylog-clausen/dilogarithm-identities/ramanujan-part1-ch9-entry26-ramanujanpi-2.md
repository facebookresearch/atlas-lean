# Ramanujan's Landen-type dilogarithm identity (Entry 26)

For real $\rho$ and $\alpha$
write $C(\rho, \alpha) = \sum_{j \ge 0} \rho^{2j+1} \cos((2j+1)\alpha) / (2j+1)^2$ and
$S(\rho, \alpha) = \sum_{j \ge 0} \rho^{2j+1} \sin((2j+1)\alpha) / (2j+1)^2$. Let
$x, y \in [0, 1]$ and $\theta, \varphi \in (-\pi, \pi]$ satisfy
$x e^{i\theta} + y e^{i\varphi} + xy\, e^{i(\theta + \varphi)} = 1$. Then the four series
defining $C(x, \theta)$, $C(y, \varphi)$, $S(x, \theta)$ and $S(y, \varphi)$ converge absolutely,
and, with the convention $\log 0 = 0$,
$C(x, \theta) + C(y, \varphi) = \pi^2/8 - \tfrac12 \log x \log y + \tfrac12 \theta\varphi$ and
$S(x, \theta) + S(y, \varphi) = -\tfrac12 \varphi \log x - \tfrac12 \theta \log y$.

Proof: Identify the odd series with Legendre's chi function, prove Landen's identity by
differentiation, and extend it to the closed right half-disk by continuity. This follows the route
in Berndt, Part I, Chapter 9, Entry 26, and Lewin, *Polylogarithms and Associated Functions*,
Chapter 1.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9, Entry 26, p. 273.
