# Settling output of a first-order stage holding a level

For real numbers $u$ (held level), $y_{\mathrm{start}}$ (initial output), $t_0$ (start of the
holding interval), $\tau$ (time constant) and $t$, the settling output is

$$y_{\mathrm{s}}(t) = u + (y_{\mathrm{start}} - u)\, e^{-(t - t_0)/\tau},$$

the held level plus the initial mismatch decayed by the exponential factor. It is meant for
$\tau > 0$ and $t \ge t_0$. The formula is defined for all real inputs: with the convention
$x/0 = 0$, $\tau = 0$ gives $y_{\mathrm{s}}(t) = y_{\mathrm{start}}$ for every $t$.
