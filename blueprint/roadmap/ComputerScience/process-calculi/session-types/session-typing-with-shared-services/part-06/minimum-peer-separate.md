# Runtime minimum guard leaf cannot own an equivalent dual peer

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $g$ a
request-free process, $e$ an endpoint with name $x$, and $c$, $d$ capabilities with $\Delta(e) = c$,
$c$ active of rank at most the rank of every active capability of $\Delta$, and $d \approx \bar c$.
If $\Gamma; \Delta \vdash_n g$ and $g$ is an output $\overline{x}\langle b\rangle.t$ or an input
$x(\cdot).t$, then $\Delta(\bar e) \ne d$.
