# Minimum guard leaf cannot own an equivalent dual peer

Let $n$ be a natural number, $\Gamma$ an ownership context, $g$ a process, $e$ an endpoint with name
$x$, and $c$, $d$ capabilities with $\Gamma(e) = c$, $c$ active, the rank of $c$ at most the rank of
every active capability of $\Gamma$, and $d \approx \bar c$. If $\Gamma \vdash^{\mathrm{rk}\simeq}_n
g$ and $g$ is an output $\overline{x}\langle b\rangle.t$ or an input $x(\cdot).t$, then $\Gamma(\bar
e) \ne d$.
