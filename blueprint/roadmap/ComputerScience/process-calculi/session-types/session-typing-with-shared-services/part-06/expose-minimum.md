# Minimum active key is the subject of a runtime frontier leaf

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
request-free guarded frontier for $\Gamma$ with $\Gamma; \Delta \vdash_n p$. Let $e$ be an endpoint
with name $x$ and $c$ an active capability with $\Delta(e) = c$ whose rank is at most the rank of
every active capability of $\Delta$. Then there are ownership contexts $\Lambda$, $\Theta$ with
disjoint domains and processes $g$, $r$ such that $\Delta = \Lambda \cup \Theta$, $\Lambda(e) = c$,
$p \equiv g \mid r$, $\Gamma; \Lambda \vdash_n g$, $\Gamma; \Theta \vdash_n r$, $r$ is a guarded
frontier for $\Gamma$, and $g$ is an output $\overline{x}\langle b\rangle.t$ or an input
$x(\cdot).t$.
