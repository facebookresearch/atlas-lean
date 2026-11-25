# Linear subject substitution with freshness from disjoint ownership

Let $n$ be a natural number, $\Delta$, $\Theta$ ownership contexts with disjoint domains, $b$ a name
scoped at depth $n$, $r$ a polarity, $c$, $c_0$, $c_1$ capabilities, $e$ an endpoint and $p$ a
process. Suppose $\Delta(b^{r}) = c$, $\Theta(e) = c_0$ and $(\uparrow_0(\Theta[e \mapsto
c_1]))[\mathrm{v}_0^{r} \mapsto c] \vdash_{n+1} p$. Then $\Theta[e \mapsto c_1][b^{r} \mapsto c]
\vdash_n p\{b\}$.
