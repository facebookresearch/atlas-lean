# First step and restarted input of the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ and $x \in \iota$. For an input
$(c, g)$, made of a [clock configuration](clock-config.md) $c$ and a sequence
$g = (g_n)_{n \in \mathbb{N}}$ of auxiliary steps, the first step and the restarted input are the
pair

$$
\Bigl(\operatorname{out}\bigl((x, c), g_0\bigr),\
\bigl(c', (g_{n+1})_{n \in \mathbb{N}}\bigr)\Bigr),
$$

where $\operatorname{out}((x, c), g_0)$ is the [step read off the first jump](output.md), $c'$ the
[clock configuration after the jump](next-clock.md) from $x$ and $(g_{n+1})_{n \in \mathbb{N}}$ the
[tail](seq-tail.md) of $g$. The first step is step $0$ of the
[steps read off the clock chain](steps.md); the restarted input, with the chain restarted at the
[next state](next.md), gives the [later steps](steps-succ.md).
