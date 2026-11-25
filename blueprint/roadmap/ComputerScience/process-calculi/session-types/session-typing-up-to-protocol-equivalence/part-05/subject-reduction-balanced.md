# Subject reduction at a balanced interface

Let $n$ be a natural number, $\Delta$ a semantically balanced ownership context (whenever $\Delta(e)
= c$, there is $d$ with $\Delta(\bar e) = d$ and $d \approx \bar c$) and $p$, $q$ processes with
$\Delta \vdash^{\simeq}_n p$ and $p \to q$. Then there is a semantically balanced ownership context
$\Xi$ with $\Xi \vdash^{\simeq}_n q$ such that $\Xi = \Delta$ or $\Xi$ is a semantic advance of
$\Delta$ (the subject endpoint and its opposite advanced past a matching send and receive, all other
entries unchanged).
