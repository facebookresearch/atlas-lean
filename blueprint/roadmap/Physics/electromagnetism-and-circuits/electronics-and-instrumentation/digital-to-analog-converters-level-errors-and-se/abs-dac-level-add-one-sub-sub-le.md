# Adjacent DAC steps are within $2\eta$ of the ideal step

Let $\Delta$ and $\eta$ be real numbers, $k_{\min}$ and $k_{\max}$ integers, and
$e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [k_{\min}, k_{\max}]$. For every integer $k$ with $k_{\min} \le k$ and $k + 1 \le k_{\max}$,
the [actual DAC levels](dac-level.md) $L(k) = \Delta k + e(k)$ satisfy

$$|L(k + 1) - L(k) - \Delta| \le 2\eta:$$

an adjacent step deviates from the ideal step $\Delta$ by at most $2\eta$ (the differential
nonlinearity bound). No sign condition on $\Delta$ is needed.
