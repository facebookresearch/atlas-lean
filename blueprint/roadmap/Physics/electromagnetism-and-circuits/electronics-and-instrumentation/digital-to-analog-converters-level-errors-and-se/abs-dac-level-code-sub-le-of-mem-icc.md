# Full-scale inputs have ADC-to-DAC error at most $\Delta/2 + \eta$

Let $\Delta > 0$ and $\eta$ be real numbers, $k_{\min}$ and $k_{\max}$ integers, and
$e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [k_{\min}, k_{\max}]$. For every input $x$ in the full-scale interval
$\Delta k_{\min} \le x \le \Delta k_{\max}$, the [actual DAC level](dac-level.md) at the saturating
code $\operatorname{code}(x) = \max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$,
where $\operatorname{round}(y) = \lfloor y + 1/2 \rfloor$ rounds to the nearest integer with ties
rounded up, satisfies $|L(\operatorname{code}(x)) - x| \le \Delta/2 + \eta$; such inputs are never
clipped. The step must be positive: for $\Delta = -2$, $k_{\min} = k_{\max} = 0$, $e \equiv 1$,
$\eta = 1$ and $x = 0$ the error is $1 > \Delta/2 + \eta = 0$.
