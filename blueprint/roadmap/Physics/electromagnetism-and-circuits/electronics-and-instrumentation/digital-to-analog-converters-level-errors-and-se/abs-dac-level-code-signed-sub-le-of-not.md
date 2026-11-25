# The signed $w$-bit ADC-to-DAC error is at most $\Delta/2 + \eta$

Let $w \ge 1$ be a natural number, $\Delta > 0$ and $\eta$ real numbers, and take the signed $w$-bit
code range $k_{\min} = -2^{w-1}$, $k_{\max} = 2^{w-1} - 1$. Let $e \colon \mathbb{Z} \to \mathbb{R}$
satisfy $|e(k)| \le \eta$ for every code in that range, and let the input $x$ be unclipped:
$-2^{w-1} \le \operatorname{round}(x/\Delta) \le 2^{w-1} - 1$, with
$\operatorname{round}(y) = \lfloor y + 1/2 \rfloor$. Then the [actual DAC level](dac-level.md) at
the saturating code
$\operatorname{code}(x) = \max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$ satisfies
$|L(\operatorname{code}(x)) - x| \le \Delta/2 + \eta$. This is the
[unclipped bound](abs-dac-level-code-sub-le-of-not-is-clip.md) for the signed code range.
