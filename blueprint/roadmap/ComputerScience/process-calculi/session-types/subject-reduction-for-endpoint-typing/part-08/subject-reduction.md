# Subject reduction for endpoint typing at compatible interfaces

Let $n$ be a natural number, $\Delta$ a compatible ownership context (whenever $\Delta(e) = c$ and
$\Delta(\bar e) = d$, then $d = \bar c$) and $p$, $q$ processes with $\Delta \vdash_n p$ (endpoint
typing) and $p \to q$. Then there is a compatible ownership context $\Xi$ with $\Xi \vdash_n q$ such
that $\Xi = \Delta$ or $\Delta$ dual-advances to $\Xi$: $\Xi = \Delta[e \mapsto (k,S')][\bar e
\mapsto (k,\overline{S'})]$ for an endpoint $e$ with $\Delta(e) = (k,S)$, $\Delta(\bar e) =
(k,\overline{S})$ and $S$ having a send head (of a name or of an endpoint) with continuation $S'$.
