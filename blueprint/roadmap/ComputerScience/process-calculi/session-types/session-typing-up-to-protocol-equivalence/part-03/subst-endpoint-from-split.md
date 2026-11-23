# Endpoint substitution with freshness from a disjoint split

Let $n$ be a natural number, $\Gamma$, $\Theta$ ownership contexts with disjoint domains, $b$ a name
scoped at depth $n$, $r$ a polarity, $c$, $v$, $c_0$, $c_1$ capabilities with $v \approx c$, $e$ an
endpoint and $p$ a process. Suppose $\Gamma(b^{r}) = v$, $\Theta(e) = c_0$ and $(\uparrow_0(\Theta[e
\mapsto c_1]))[\mathrm{v}_0^{r} \mapsto c] \vdash^{\simeq}_{n+1} p$. Then $\Theta[e \mapsto
c_1][b^{r} \mapsto v] \vdash^{\simeq}_n p\{b\}$.
