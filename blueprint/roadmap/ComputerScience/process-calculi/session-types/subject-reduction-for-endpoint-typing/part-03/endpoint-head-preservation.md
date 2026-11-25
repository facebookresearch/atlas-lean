# Endpoint-delegating communication preserves typing

Let $n$, $j$ be natural numbers, $\Delta$, $\Theta$ ownership contexts with disjoint domains such
that $\Delta \cup \Theta$ is compatible, $e \ne d$ endpoints, $x$ the name of $e$, $y$ the name of
$d$ (scoped at depth $n$), $r$ the polarity of $d$, $c = (k,S)$ a capability, $T$, $S'$ protocols
and $p$, $q$ processes. If $\Delta(e) = c$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\Delta(d) = (j,T)$,
$(\Delta \setminus d)[e \mapsto (k,S')] \vdash_n p$ and $\Theta \vdash_n x(\cdot).q$, then

$$
(\Delta \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,\overline{S'})] \vdash_n p \mid q\{y\}.
$$
