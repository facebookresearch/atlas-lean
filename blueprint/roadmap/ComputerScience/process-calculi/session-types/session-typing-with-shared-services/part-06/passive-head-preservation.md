# Passive head communication preserves runtime typing

Let $n$ be a natural number, $\Gamma$ a service environment, $\Lambda$, $\Theta$ ownership contexts
with disjoint domains such that $\Lambda$ is separated from $\Gamma$ and $\Lambda \cup \Theta$ is
semantically compatible, $e$ an endpoint with name $x$, $c = (k,S)$ a capability, $S'$ a protocol,
$b$ a name scoped at depth $n$ and $p$, $q$ processes. Suppose $\Lambda(e) = c$, $\mathrm{unf}(S) =
{!\mathrm{N}}.S'$, $\Gamma; \Lambda[e \mapsto (k,S')] \vdash_n p$ and $\Gamma; \Theta \vdash_n
x(\cdot).q$. Then there are a capability $d = (k,U)$ and a protocol $U'$ with $\Theta(\bar e) = d$,
$\mathrm{unf}(U) = {?\mathrm{N}}.U'$, $U' \simeq \overline{S'}$ and

$$
\Gamma; (\Lambda \cup \Theta)[e \mapsto (k,S')][\bar e \mapsto (k,U')] \vdash_n p \mid q\{b\}.
$$
