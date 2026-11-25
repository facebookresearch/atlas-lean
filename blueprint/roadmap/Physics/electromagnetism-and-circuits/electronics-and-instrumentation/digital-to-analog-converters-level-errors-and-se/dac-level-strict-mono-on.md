# For $2\eta < \Delta$, the DAC levels are strictly increasing

Let $\Delta$ and $\eta$ be real numbers with $2\eta < \Delta$, $k_{\min}$ and $k_{\max}$ integers,
and $e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [k_{\min}, k_{\max}]$. Then the [actual DAC level](dac-level.md) $L(k) = \Delta k + e(k)$ is
strictly increasing on the integer codes of $[k_{\min}, k_{\max}]$: $L(a) < L(b)$ for codes $a < b$.
The threshold is sharp: for $0 < \Delta \le 2\eta$
[suitable errors make two levels equal](exists-not-strict-mono-on-of-le-two-mul.md).
