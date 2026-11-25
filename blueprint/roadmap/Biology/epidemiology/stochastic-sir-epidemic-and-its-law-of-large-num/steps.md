# Steps read off the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$, $x \in \iota$, $c$ a
[clock configuration](clock-config.md) and $g = (g_n)_{n \in \mathbb{N}}$ a sequence of auxiliary
steps $g_n = (\eta_n, e_n)$, with $\eta_n : \iota \to \iota$ and $e_n \in \mathbb{R}$. Let
$(x_n, c_n)$ be the [state and clocks after $n$ jumps](config.md) from $(x_0, c_0) = (x, c)$. The
steps read off the clock chain started at $x$ with clocks $c$ and auxiliary steps $g$ form the step
sequence $\omega(x, c, g) = (\omega_n)_{n \in \mathbb{N}}$ with

$$\omega_n = \operatorname{out}\bigl((x_n, c_n), g_n\bigr),$$

where $\operatorname{out}$ is the [step read off one jump](output.md). Thus
$\omega_n = (\xi_n, E_n)$ with $\xi_n(x_n) = x_{n+1}$ and $\xi_n(y) = \eta_n(y)$ for $y \ne x_n$,
and $E_n = q(x_n)\, h(x_n, r^{(n)})$ if $q(x_n) \ne 0$, $E_n = e_n$ if $q(x_n) = 0$, where $q$ is
the [total rate](total-rate.md), $h$ the [holding time](hold.md) and $r^{(n)}$ the residual clocks
of $c_n$.
