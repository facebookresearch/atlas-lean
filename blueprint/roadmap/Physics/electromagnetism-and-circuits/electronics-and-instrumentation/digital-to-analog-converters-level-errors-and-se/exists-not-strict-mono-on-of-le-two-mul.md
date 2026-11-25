# For $\Delta \le 2\eta$, level errors can break strict monotonicity

For all real numbers $\Delta > 0$ and $\eta$ with $\Delta \le 2\eta$, there is a level error $e$
with $|e(k)| \le \eta$ for the codes $k = 0, 1$ such that the [actual DAC levels](dac-level.md)
$L(k) = \Delta k + e(k)$ are not strictly increasing on $\{0, 1\}$: with $e(0) = \Delta/2$ and
$e(k) = -\Delta/2$ for $k \ne 0$, both levels equal $\Delta/2$. So the condition $2\eta < \Delta$ of
[strict monotonicity](dac-level-strict-mono-on.md) is sharp.
