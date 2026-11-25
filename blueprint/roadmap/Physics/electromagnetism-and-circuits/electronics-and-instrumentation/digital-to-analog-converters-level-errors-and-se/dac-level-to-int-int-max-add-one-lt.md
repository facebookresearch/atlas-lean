# For $2\eta < \Delta$, signed wraparound at full scale lowers the level

Let $w \ge 1$ be a natural number, $\Delta$ and $\eta$ real numbers with $2\eta < \Delta$, and
$e \colon \mathbb{Z} \to \mathbb{R}$ a level error with $|e(k)| \le \eta$ for every code
$k \in [-2^{w-1}, 2^{w-1} - 1]$. In $w$-bit two's-complement arithmetic, adding $1$ to the largest
signed value $2^{w-1} - 1$ wraps around to the smallest, $-2^{w-1}$. This successor does not decode
to the next integer $2^{w-1}$, and its [actual DAC level](dac-level.md) is strictly lower:
$L(-2^{w-1}) < L(2^{w-1} - 1)$. So the wraparound is not an adjacent step of a monotone DAC.
