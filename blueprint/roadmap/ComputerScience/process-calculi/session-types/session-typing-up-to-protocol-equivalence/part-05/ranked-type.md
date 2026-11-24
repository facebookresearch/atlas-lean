# Priority-ranked conversion typing judgement

Conversion ranked typing $\Delta \vdash^{\mathrm{rk}\simeq}_n p$ is defined by the rules of ranked
typing with the conversion rule for endpoint output. With $\mathrm{unf}(S)$ the head of $S$,
"scoped" meaning scoped at depth $n$, and $\mathrm{Min}_\Delta(e,k)$ meaning that every endpoint $d
\ne e$ with an active capability (head not $\mathrm{end}$) in $\Delta$ has rank $> k$:

- if every capability of $\Delta$ has head $\mathrm{end}$ and every endpoint of $\Delta$ has a
  scoped name, then $\Delta \vdash^{\mathrm{rk}\simeq}_n \mathbf{0}$;
- if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, the name
  $x$ of $e$ and the name $b$ are scoped and $\Delta[e \mapsto (k,S')] \vdash^{\mathrm{rk}\simeq}_n
  p$, then $\Delta \vdash^{\mathrm{rk}\simeq}_n \overline{x}\langle b\rangle.p$;
- if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) = {?\mathrm{N}}.S'$, $x$ is
  scoped and $\uparrow_0(\Delta[e \mapsto (k,S')]) \vdash^{\mathrm{rk}\simeq}_{n+1} p$, then $\Delta
  \vdash^{\mathrm{rk}\simeq}_n x(\cdot).p$;
- if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $d$ is an
  endpoint of polarity $r$ with $\Delta(d) = v \approx (j,T)$, $e \ne d$, the names $x$ of $e$ and
  $y$ of $d$ are scoped and $(\Delta \setminus d)[e \mapsto (k,S')] \vdash^{\mathrm{rk}\simeq}_n p$,
  then $\Delta \vdash^{\mathrm{rk}\simeq}_n \overline{x}\langle y\rangle.p$;
- if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) = {?(r,j,T)}.S'$, $x$ is
  scoped and $\uparrow_0(\Delta[e \mapsto (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)]
  \vdash^{\mathrm{rk}\simeq}_{n+1} p$, then $\Delta \vdash^{\mathrm{rk}\simeq}_n x(\cdot).p$;
- if $\Delta$, $\Theta$ have disjoint domains, $\Delta \vdash^{\mathrm{rk}\simeq}_n p$ and $\Theta
  \vdash^{\mathrm{rk}\simeq}_n q$, then $\Delta \cup \Theta \vdash^{\mathrm{rk}\simeq}_n p \mid q$;
- if $\nu_c\Delta \vdash^{\mathrm{rk}\simeq}_{n+1} p$ for a capability $c$, then $\Delta
  \vdash^{\mathrm{rk}\simeq}_n \nu\,p$.

Here $\approx$ is capability equivalence (equal ranks, tree-equivalent protocols), $\uparrow_0$
raises every variable name index of an endpoint by one, and $\nu_c\Delta$ is $\uparrow_0\Delta$
extended by $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
