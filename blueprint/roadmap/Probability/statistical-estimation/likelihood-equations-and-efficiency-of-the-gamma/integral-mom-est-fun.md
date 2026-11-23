# The moment equations hold at the truth

Let $\mu_X$ be a probability measure on $\mathbb{N}$, the law of a count $K$, and write $E$ for
expectations under $\mu_X$. Let $b > 0$, let $a$ and $\sigma$ be real, let $E K^2 < \infty$, and let
$K$ have the negative binomial mean and second moment at $(a, b)$: $E K = m$ and
$E K^2 = m + m^2 / a + m^2$, with $m = \sigma a / b$ (where $m^2 / a = 0$ for $a = 0$, by the
convention $x / 0 = 0$). Then the [moment estimating function](mom-est-fun.md) $g_\sigma(\theta, k)$
has mean zero at $(a, b)$: $E\bigl[g_\sigma((a, b), K)\bigr] = 0$.
