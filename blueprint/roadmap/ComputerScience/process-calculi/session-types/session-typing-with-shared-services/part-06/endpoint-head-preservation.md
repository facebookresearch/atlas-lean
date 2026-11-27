# Endpoint head communication preserves runtime typing

Let $n$, $j$ be natural numbers, $\Gamma$ a service environment, $\Lambda$, $\Theta$ ownership
contexts with disjoint domains such that $\Lambda$ is separated from $\Gamma$ and $\Lambda \cup
\Theta$ is semantically compatible, $e \ne f$ endpoints, $x$ the name of $e$, $y$ the name of $f$
(scoped at depth $n$), $r$ the polarity of $f$, $c = (k,S)$ and $v$ capabilities, $T$, $S'$
protocols and $p$, $q$ processes. Suppose $\Lambda(e) = c$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$,
$\Lambda(f) = v \approx (j,T)$, $\Gamma; (\Lambda \setminus f)[e \mapsto (k,S')] \vdash_n p$ and
$\Gamma; \Theta \vdash_n x(\cdot).q$. Then there are a capability $d = (k,U)$ and protocols $T'$,
$U'$ with $\Theta(\bar e) = d$, $\mathrm{unf}(U) = {?(r,j,T')}.U'$, $T' \simeq T$, $U' \simeq
\overline{S'}$ and

$$
\Gamma; (\Lambda \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,U')] \vdash_n p \mid q\{y\}.
$$
