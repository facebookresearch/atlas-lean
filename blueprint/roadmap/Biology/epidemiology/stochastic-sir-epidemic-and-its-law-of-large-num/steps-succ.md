# The steps after the first are those of the restarted chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$, $x \in \iota$, $c$ a
[clock configuration](clock-config.md), $g = (g_n)_{n \in \mathbb{N}}$ a sequence of auxiliary
steps, and $(x_1, c_1)$ the [state and clocks after one jump](config.md) from $(x, c)$: the
[next state](next.md) and the [clock configuration after the jump](next-clock.md). Write
$\omega(x, c, g)$ for the [steps read off the clock chain](steps.md) started at $x$ with clocks $c$
and auxiliary steps $g$. For every $n \in \mathbb{N}$,

$$\omega_{n+1}(x, c, g) = \omega_n\bigl(x_1, c_1, (g_{m+1})_{m \in \mathbb{N}}\bigr):$$

step $n + 1$ is step $n$ of the chain restarted at $x_1$ with clocks $c_1$ and the
[tail](seq-tail.md) $(g_1, g_2, \dots)$ of the auxiliary steps.
