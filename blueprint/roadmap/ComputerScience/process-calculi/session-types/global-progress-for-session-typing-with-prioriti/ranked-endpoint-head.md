# Endpoint delegation at the head preserves ranked typing

Let $n$, $j$ be natural numbers, $\Delta$, $\Theta$ ownership contexts with disjoint domains, $e \ne
d$ endpoints, $x$ the name of $e$, $y$ the name of $d$ (scoped at depth $n$), $r$ the polarity of
$d$, $c = (k,S)$ a capability, $T$, $S'$ protocols and $p$, $q$ processes. Suppose $\Delta(e) = c$,
$\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\Delta(d) = (j,T)$, $(\Delta \setminus d)[e \mapsto (k,S')]
\vdash^{\mathrm{rk}}_n p$, $\Theta \vdash^{\mathrm{rk}}_n x(\cdot).q$, and $\Delta \cup \Theta$ is
compatible (opposite endpoints present in it carry dual capabilities). Then

$$
(\Delta \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,\overline{S'})] \vdash^{\mathrm{rk}}_n p \mid q\{y\}.
$$
