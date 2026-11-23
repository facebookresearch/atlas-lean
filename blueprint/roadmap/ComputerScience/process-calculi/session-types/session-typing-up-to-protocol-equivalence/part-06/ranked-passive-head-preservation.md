# Passive head communication preserves conversion ranked typing

Let $n$ be a natural number, $\Gamma$, $\Theta$ ownership contexts with disjoint domains such that
$\Gamma \cup \Theta$ is semantically compatible, $e$ an endpoint with name $x$, $c = (k,S)$ a
capability, $S'$ a protocol, $b$ a name scoped at depth $n$ and $p$, $q$ processes. Suppose
$\Gamma(e) = c$, $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, $\Gamma[e \mapsto (k,S')]
\vdash^{\mathrm{rk}\simeq}_n p$ and $\Theta \vdash^{\mathrm{rk}\simeq}_n x(\cdot).q$. Then there are
a capability $d = (k,U)$ and a protocol $U'$ with $\Theta(\bar e) = d$, $\mathrm{unf}(U) =
{?\mathrm{N}}.U'$, $U' \simeq \overline{S'}$ and

$$
(\Gamma \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,U')] \vdash^{\mathrm{rk}\simeq}_n p \mid q\{b\}.
$$
