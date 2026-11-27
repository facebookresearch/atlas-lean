# Passive-payload communication preserves endpoint typing

Let $n$ be a natural number, $\Delta$, $\Theta$ ownership contexts with disjoint domains such that
$\Delta \cup \Theta$ is compatible, $e$ an endpoint with name $x$, $c = (k,S)$ a capability, $S'$ a
protocol, $b$ a name scoped at depth $n$ and $p$, $q$ processes. If $\Delta(e) = c$,
$\mathrm{unf}(S) = {!\mathrm{N}}.S'$, $\Delta[e \mapsto (k,S')] \vdash_n p$ and $\Theta \vdash_n
x(\cdot).q$, then

$$
(\Delta \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,\overline{S'})] \vdash_n p \mid q\{b\}.
$$
