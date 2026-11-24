# The reactor field in deviation variables is the linear system's field

Let $V > 0$, $Q > 0$ and $k \ge 0$, and let $(c_{ss}, c_{\mathrm{in},ss})$ be a steady pair:
$\frac{Q}{V}(c_{\mathrm{in},ss} - c_{ss}) - k\, c_{ss} = 0$. Then for every deviation $x$ of the
concentration and $u$ of the inlet concentration, the reactor right-hand side at the deviated
values,

$$\frac{Q}{V}\big((c_{\mathrm{in},ss} + u) - (c_{ss} + x)\big) - k\,(c_{ss} + x),$$

equals

$$-\Big(\frac{Q}{V} + k\Big) x + \frac{Q}{V}\, u,$$

the field of the [stirred-tank linear system](cstr-linear-system.md) with output gain $1$ at state
$x$ and input $u$. The correspondence is exact: there is no linearisation remainder. The algebra
uses only the steady-pair equation; the positivity conditions are the physical domain.
