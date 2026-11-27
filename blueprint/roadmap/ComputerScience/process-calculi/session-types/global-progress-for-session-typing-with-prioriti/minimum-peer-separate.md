# Minimum guard leaf cannot own its dual peer

Let $n$ be a natural number, $\Gamma$ an ownership context, $g$ a process, $e$ an endpoint with name
$x$ and opposite endpoint $\bar e$, and $c$ an active capability with $\Gamma(e) = c$ whose rank is
at most the rank of every active capability of $\Gamma$. If $\Gamma \vdash^{\mathrm{rk}}_n g$ and
$g$ is an output $\overline{x}\langle b\rangle.t$ or an input $x(\cdot).t$, then $\Gamma(\bar e) \ne
\bar c$.
