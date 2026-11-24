# Endpoint substitution with side conditions derived from a split

Let $n$ be a natural number, $\Gamma$ a service environment, $\Lambda$, $\Theta$ ownership contexts
with disjoint domains and $\Lambda$ separated from $\Gamma$, $b$ a name scoped at depth $n$, $r$ a
polarity, $c$, $v$, $c_0$, $c_1$ capabilities with $v \approx c$, $e$ an endpoint and $p$ a process.
Suppose $\Lambda(b^{r}) = v$, $\Theta(e) = c_0$ and $\Gamma; (\uparrow_0(\Theta[e \mapsto
c_1]))[\mathrm{v}_0^{r} \mapsto c] \vdash_{n+1} p$. Then $\Gamma; \Theta[e \mapsto c_1][b^{r}
\mapsto v] \vdash_n p\{b\}$.
