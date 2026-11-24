# Endpoint head communication preserves conversion ranked typing

Let $n$, $j$ be natural numbers, $\Gamma$, $\Theta$ ownership contexts with disjoint domains such
that $\Gamma \cup \Theta$ is semantically compatible, $e \ne f$ endpoints, $x$ the name of $e$, $y$
the name of $f$ (scoped at depth $n$), $r$ the polarity of $f$, $c = (k,S)$ and $v$ capabilities,
$T$, $S'$ protocols and $p$, $q$ processes. Suppose $\Gamma(e) = c$, $\mathrm{unf}(S) =
{!(r,j,T)}.S'$, $\Gamma(f) = v \approx (j,T)$, $(\Gamma \setminus f)[e \mapsto (k,S')]
\vdash^{\mathrm{rk}\simeq}_n p$ and $\Theta \vdash^{\mathrm{rk}\simeq}_n x(\cdot).q$. Then there are
a capability $d = (k,U)$ and protocols $T'$, $U'$ with $\Theta(\bar e) = d$, $\mathrm{unf}(U) =
{?(r,j,T')}.U'$, $T' \simeq T$, $U' \simeq \overline{S'}$ and

$$
(\Gamma \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,U')] \vdash^{\mathrm{rk}\simeq}_n p \mid q\{y\}.
$$
