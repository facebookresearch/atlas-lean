# The unclipped ADC-to-DAC error is at most $\Delta/2 + \eta$

Let $\Delta > 0$ and $\eta$ be real numbers, $k_{\min}$ and $k_{\max}$ integers, and
$e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [k_{\min}, k_{\max}]$. The saturating analog-to-digital converter sends an input $x$ to
the code $\operatorname{code}(x) = \max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$,
where
$\operatorname{round}(y) = \lfloor y + 1/2 \rfloor$ rounds to the nearest integer with ties rounded
up; it clips $x$ when $\operatorname{round}(x/\Delta) < k_{\min}$ or
$\operatorname{round}(x/\Delta) > k_{\max}$. For every input $x$ that is not clipped, the
[actual DAC level](dac-level.md) at its code satisfies

$$|L(\operatorname{code}(x)) - x| \le \frac{\Delta}{2} + \eta:$$

the rounding error contributes at most $\Delta/2$ and the level error at most $\eta$.
