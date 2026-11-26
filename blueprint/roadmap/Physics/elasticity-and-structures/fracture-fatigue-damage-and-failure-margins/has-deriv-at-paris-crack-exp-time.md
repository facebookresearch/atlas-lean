# Up to failure the event path $a(f t)$ solves $da/dt = f K a$

Let $K$, $a_0$, $K_{IC}$, $Y$ and $\sigma$ be real numbers and $f > 0$, let $a(N) = a_0 e^{K N}$ be
the [logarithmic-branch solution](paris-crack-exp.md) and $N_f = \log(a_c / a_0)/K$ its [Paris
life](paris-life-exp.md), with $a_c = (K_{IC}/(Y\sigma))^2/\pi$ the [critical crack
length](critical-crack-length.md). For every time $t$ with $0 \le t \le N_f / f$, the [event
path](saturated-crack-path.md) at $t$ is the crack after $f t$ cycles, $a(\min(f t, N_f)) = a(f t)$,
and the crack in time $s \mapsto a(f s)$ (for real $s$) has at $t$ the derivative

$$\frac{d}{ds}\, a(f s) \Big|_{s = t} = f K\, a(f t) ,$$

the Paris law $da/dN = K a$ at $f$ cycles per unit time. The derivative is that of
$s \mapsto a(f s)$; the event path equals it up to the failure time $N_f / f$ and is constant
afterwards. No condition on $K$, $a_0$ or $a_c$ is needed: with the conventions $x / 0 = 0$,
$\log 0 = 0$ and $\log x = \log |x|$ the life $N_f$ is a real number for all inputs, and when
$N_f < 0$ no time satisfies $0 \le t \le N_f / f$. In the model $K > 0$ and $0 < a_0 < a_c$, so that
$N_f > 0$.
