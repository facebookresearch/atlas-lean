# Inversion of runtime input on a nonshared subject

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $a$ a
name that is not a declared trigger $\mathrm{c}_s$, and $p$ a process with $\Gamma; \Delta \vdash_n
a(\cdot).p$. Then there are an endpoint $e$ with name $a$ and a capability $c = (k,S)$ with
$\Delta(e) = c$ such that either

- $\mathrm{unf}(S) = {?\mathrm{N}}.S'$ and $\Gamma; \uparrow_0(\Delta[e \mapsto (k,S')])
  \vdash_{n+1} p$ for some protocol $S'$, or
- $\mathrm{unf}(S) = {?(r,j,T)}.S'$ and $\Gamma; \uparrow_0(\Delta[e \mapsto
  (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)] \vdash_{n+1} p$ for some polarity $r$, rank $j$ and
  protocols $T$, $S'$.
