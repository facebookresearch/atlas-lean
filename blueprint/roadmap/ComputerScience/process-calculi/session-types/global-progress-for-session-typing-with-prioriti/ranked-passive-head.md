# Passive head communication preserves ranked typing

Let $n$ be a natural number, $\Delta$, $\Theta$ ownership contexts with disjoint domains, $e$ an
endpoint with name $x$ and opposite endpoint $\bar e$, $c = (k,S)$ a capability, $S'$ a protocol,
$b$ a name scoped at depth $n$ and $p$, $q$ processes. Suppose $\Delta(e) = c$, $\mathrm{unf}(S) =
{!\mathrm{N}}.S'$, $\Delta[e \mapsto (k,S')] \vdash^{\mathrm{rk}}_n p$, $\Theta
\vdash^{\mathrm{rk}}_n x(\cdot).q$, and $\Delta \cup \Theta$ is compatible (whenever it maps an
endpoint to $c'$ and its opposite to $d'$, then $d' = \bar{c'}$). Then

$$
(\Delta \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,\overline{S'})] \vdash^{\mathrm{rk}}_n p \mid q\{b\}.
$$
