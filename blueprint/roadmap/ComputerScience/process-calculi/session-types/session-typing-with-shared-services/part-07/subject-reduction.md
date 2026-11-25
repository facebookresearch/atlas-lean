# Subject reduction for runtime typing at compatible interfaces

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ a semantically compatible
ownership context (whenever $\Delta(e) = c$ and $\Delta(\bar e) = d$, then $d \approx \bar c$) and
$p$, $q$ processes with $\Gamma; \Delta \vdash_n p$ and $p \to q$. Then there is a semantically
compatible ownership context $\Xi$ with $\Gamma; \Xi \vdash_n q$ such that $\Xi = \Delta$ or $\Xi$
is a semantic advance of $\Delta$ (an endpoint and its opposite advanced past a matching send and
receive, with tree-equivalent dual continuations, all other entries unchanged).
