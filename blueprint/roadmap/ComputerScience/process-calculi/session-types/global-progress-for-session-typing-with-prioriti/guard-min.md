# Guard priority condition on active endpoints

Let $\Delta$ be an ownership context (a finite map from endpoints, i.e. names with a polarity $+$ or
$-$, to capabilities, i.e. pairs of a rank in $\mathbb{N}$ and a protocol), $e$ an endpoint and $k$
a natural number. The guard condition $\mathrm{Min}_\Delta(e,k)$ holds when every endpoint $d \ne e$
that $\Delta$ maps to an active capability (one whose protocol does not have head $\mathrm{end}$)
has rank strictly greater than $k$. The head of a protocol is its first action, or $\mathrm{end}$,
after unrolling a recursive protocol presented by a finite graph once.
