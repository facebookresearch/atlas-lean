# Inversion of conversion-ranked input typing

Let $n$ be a natural number, $\Delta$ an ownership context, $a$ a name and $p$ a process with
$\Delta \vdash^{\mathrm{rk}\simeq}_n a(\cdot).p$. Then there are an endpoint $e$ with name $a$ and a
capability $c = (k,S)$ with $\Delta(e) = c$ such that either

- $\mathrm{unf}(S) = {?\mathrm{N}}.S'$ and $\uparrow_0(\Delta[e \mapsto (k,S')])
  \vdash^{\mathrm{rk}\simeq}_{n+1} p$ for some protocol $S'$, or
- $\mathrm{unf}(S) = {?(r,j,T)}.S'$ and $\uparrow_0(\Delta[e \mapsto (k,S')])[\mathrm{v}_0^{r}
  \mapsto (j,T)] \vdash^{\mathrm{rk}\simeq}_{n+1} p$ for some polarity $r$, rank $j$ and protocols
  $T$, $S'$.
