# Priority-ranked endpoint typing judgement

Ranked typing $\Delta \vdash^{\mathrm{rk}}_n p$ relates a natural number $n$ (the number of
enclosing binders), an ownership context $\Delta$ (a finite map from endpoints $x^{r}$, a name $x$
with polarity $r \in \{+,-\}$, to capabilities $(k,S)$ of rank $k$ and protocol $S$) and a process
$p$. It is defined inductively by the following rules, where the head $\mathrm{unf}(S)$ of a
protocol is its first action or $\mathrm{end}$ (a graph-presented recursive protocol is unrolled
once), $\mathrm{Min}_\Delta(e,k)$ says that every endpoint $d \ne e$ with an active capability in
$\Delta$ has rank $> k$, and "scoped" means scoped at depth $n$.

- If every capability of $\Delta$ has head $\mathrm{end}$ and every endpoint of $\Delta$ has a
  scoped name, then $\Delta \vdash^{\mathrm{rk}}_n \mathbf{0}$.
- Passive output: if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) =
  {!\mathrm{N}}.S'$, the name $x$ of $e$ and the payload $b$ are scoped and $\Delta[e \mapsto
  (k,S')] \vdash^{\mathrm{rk}}_n p$, then $\Delta \vdash^{\mathrm{rk}}_n \overline{x}\langle
  b\rangle.p$.
- Passive input: if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) =
  {?\mathrm{N}}.S'$, the name $x$ of $e$ is scoped and $\uparrow_0(\Delta[e \mapsto (k,S')])
  \vdash^{\mathrm{rk}}_{n+1} p$, then $\Delta \vdash^{\mathrm{rk}}_n x(\cdot).p$.
- Endpoint output: if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) =
  {!(r,j,T)}.S'$, $d$ is an endpoint with polarity $r$, $\Delta(d) = (j,T)$, $e \ne d$, the names
  $x$ of $e$ and $y$ of $d$ are scoped and $(\Delta \setminus d)[e \mapsto (k,S')]
  \vdash^{\mathrm{rk}}_n p$, then $\Delta \vdash^{\mathrm{rk}}_n \overline{x}\langle y\rangle.p$.
- Endpoint input: if $\Delta(e) = (k,S)$, $\mathrm{Min}_\Delta(e,k)$, $\mathrm{unf}(S) =
  {?(r,j,T)}.S'$, the name $x$ of $e$ is scoped and $\uparrow_0(\Delta[e \mapsto
  (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)] \vdash^{\mathrm{rk}}_{n+1} p$, then $\Delta
  \vdash^{\mathrm{rk}}_n x(\cdot).p$.
- If $\Delta$ and $\Theta$ have disjoint domains, $\Delta \vdash^{\mathrm{rk}}_n p$ and $\Theta
  \vdash^{\mathrm{rk}}_n q$, then $\Delta \cup \Theta \vdash^{\mathrm{rk}}_n p \mid q$.
- If $c$ is a capability and $\nu_c\Delta \vdash^{\mathrm{rk}}_{n+1} p$, then $\Delta
  \vdash^{\mathrm{rk}}_n \nu\,p$.

Here $\uparrow_0\Delta$ adds one to the index of every variable name of an endpoint of $\Delta$,
$\nu_c\Delta$ is $\uparrow_0\Delta$ extended with $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-}
\mapsto \bar c$ ($\bar c$ has the same rank and the dual protocol), the input $x(\cdot).p$ binds the
variable $\mathrm{v}_0$ in $p$, and $\Delta \setminus d$ removes $d$. Without the guard conditions
these are exactly the rules of endpoint typing.
