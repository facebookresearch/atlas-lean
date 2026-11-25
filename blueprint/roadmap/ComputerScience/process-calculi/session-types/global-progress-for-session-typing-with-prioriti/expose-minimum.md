# Minimum active role is the subject of a frontier leaf

Let $n$ be a natural number, $\Delta$ an ownership context and $p$ a guard frontier with $\Delta
\vdash^{\mathrm{rk}}_n p$. Let $e$ be an endpoint with name $x$ and $c$ an active capability with
$\Delta(e) = c$ whose rank is at most the rank of every active capability of $\Delta$. Then there
are ownership contexts $\Gamma$, $\Theta$ with disjoint domains and processes $g$, $r$ such that
$\Delta = \Gamma \cup \Theta$, $\Gamma(e) = c$, $p \equiv g \mid r$, $\Gamma \vdash^{\mathrm{rk}}_n
g$, $\Theta \vdash^{\mathrm{rk}}_n r$, $r$ is a guard frontier, and $g$ is an output
$\overline{x}\langle b\rangle.t$ or an input $x(\cdot).t$ for some name $b$ and process $t$.
