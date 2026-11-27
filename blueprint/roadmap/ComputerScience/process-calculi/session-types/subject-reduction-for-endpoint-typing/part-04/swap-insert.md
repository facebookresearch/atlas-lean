# Context swapping commutes with insertion

For every natural number $k$, ownership context $\Delta$, endpoint $x^{r}$ and capability $c$,
$(\Delta[x^{r} \mapsto c])[k \leftrightarrow k+1] = (\Delta[k \leftrightarrow k+1])[(x[k
\leftrightarrow k+1])^{r} \mapsto c]$.
