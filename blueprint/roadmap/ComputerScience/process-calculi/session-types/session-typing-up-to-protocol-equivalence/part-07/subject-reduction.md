# Conversion ranked subject reduction at compatible interfaces

Let $n$ be a natural number, $\Delta$ a semantically compatible ownership context (whenever
$\Delta(e) = c$ and $\Delta(\bar e) = d$, then $d \approx \bar c$) and $p$, $q$ processes with
$\Delta \vdash^{\mathrm{rk}\simeq}_n p$ and $p \to q$. Then there is a semantically compatible
ownership context $\Xi$ with $\Xi \vdash^{\mathrm{rk}\simeq}_n q$ such that $\Xi = \Delta$ or $\Xi$
is a semantic advance of $\Delta$ (the subject endpoint and its opposite advanced past a matching
send and receive, with tree-equivalent dual continuations, all other entries unchanged).
