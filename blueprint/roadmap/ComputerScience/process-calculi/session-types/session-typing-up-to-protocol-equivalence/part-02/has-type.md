# Conversion-enabled endpoint typing judgement

Conversion typing $\Delta \vdash^{\simeq}_n p$, for a natural number $n$, an ownership context
$\Delta$ and a process $p$, is defined by the same rules as endpoint typing except for endpoint
output. With $\mathrm{unf}(S)$ the head of $S$ and "scoped" meaning scoped at depth $n$:

- if every capability of $\Delta$ has head $\mathrm{end}$ and every endpoint of $\Delta$ has a
  scoped name, then $\Delta \vdash^{\simeq}_n \mathbf{0}$;
- if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, the name $x$ of $e$ and the name $b$
  are scoped and $\Delta[e \mapsto (k,S')] \vdash^{\simeq}_n p$, then $\Delta \vdash^{\simeq}_n
  \overline{x}\langle b\rangle.p$;
- if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {?\mathrm{N}}.S'$, $x$ is scoped and
  $\uparrow_0(\Delta[e \mapsto (k,S')]) \vdash^{\simeq}_{n+1} p$, then $\Delta \vdash^{\simeq}_n
  x(\cdot).p$;
- if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $d$ is an endpoint of polarity $r$ with
  $\Delta(d) = v$ and $v \approx (j,T)$, $e \ne d$, the names $x$ of $e$ and $y$ of $d$ are scoped
  and $(\Delta \setminus d)[e \mapsto (k,S')] \vdash^{\simeq}_n p$, then $\Delta \vdash^{\simeq}_n
  \overline{x}\langle y\rangle.p$;
- if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {?(r,j,T)}.S'$, $x$ is scoped and $\uparrow_0(\Delta[e
  \mapsto (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)] \vdash^{\simeq}_{n+1} p$, then $\Delta
  \vdash^{\simeq}_n x(\cdot).p$;
- if $\Delta$, $\Theta$ have disjoint domains, $\Delta \vdash^{\simeq}_n p$ and $\Theta
  \vdash^{\simeq}_n q$, then $\Delta \cup \Theta \vdash^{\simeq}_n p \mid q$;
- if $\nu_c\Delta \vdash^{\simeq}_{n+1} p$ for a capability $c$, then $\Delta \vdash^{\simeq}_n
  \nu\,p$.

Here $v \approx (j,T)$ means equal ranks and tree-equivalent protocols, $\uparrow_0$ raises every
variable name index of an endpoint by one, and $\nu_c\Delta$ is $\uparrow_0\Delta$ extended by
$\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
