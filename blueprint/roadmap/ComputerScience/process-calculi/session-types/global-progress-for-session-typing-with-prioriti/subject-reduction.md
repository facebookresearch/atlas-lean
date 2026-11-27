# Subject reduction for ranked typing at compatible interfaces

Let $n$ be a natural number, $\Delta$ a compatible ownership context (opposite endpoints present in
it carry dual capabilities) and $p$, $q$ processes with $\Delta \vdash^{\mathrm{rk}}_n p$ and $p \to
q$. Then there is a compatible ownership context $\Xi$ with $\Xi \vdash^{\mathrm{rk}}_n q$ such that
$\Xi = \Delta$ or $\Xi$ is a dual advance of $\Delta$: $\Xi = \Delta[e \mapsto (k,S')][\bar e
\mapsto (k,\overline{S'})]$ for an endpoint $e$ with $\Delta(e) = (k,S)$, $\Delta(\bar e) =
(k,\overline{S})$ and $\mathrm{unf}(S)$ a send (of a name or of an endpoint) with continuation $S'$.
