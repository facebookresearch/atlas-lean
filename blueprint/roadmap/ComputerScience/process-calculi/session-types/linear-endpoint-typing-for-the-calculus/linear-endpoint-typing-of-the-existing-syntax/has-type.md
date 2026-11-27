# Linear endpoint typing of π-calculus processes

Endpoint typing $\Delta \vdash_n p$ relates a natural number $n$ (the number of enclosing binders),
an ownership context $\Delta$ (a finite map from endpoints $x^{r}$, a name $x$ with polarity $r \in
\{+,-\}$, to capabilities $(k,S)$ of rank $k$ and protocol $S$) and a π-calculus process $p$. It is
defined inductively by the following rules, where $\mathrm{unf}(S)$ is the head of $S$ (its first
action or $\mathrm{end}$, a graph-presented recursive protocol being unrolled once) and "scoped"
means scoped at depth $n$ (a constant, or a variable with index $< n$).

- If every capability of $\Delta$ has head $\mathrm{end}$ and every endpoint of $\Delta$ has a
  scoped name, then $\Delta \vdash_n \mathbf{0}$.
- Passive output: if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, the name $x$ of $e$
  and the payload $b$ are scoped and $\Delta[e \mapsto (k,S')] \vdash_n p$, then $\Delta \vdash_n
  \overline{x}\langle b\rangle.p$.
- Passive input: if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {?\mathrm{N}}.S'$, the name $x$ of $e$
  is scoped and $\uparrow_0(\Delta[e \mapsto (k,S')]) \vdash_{n+1} p$, then $\Delta \vdash_n
  x(\cdot).p$.
- Endpoint output: if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $d$ is an endpoint of
  polarity $r$ with $\Delta(d) = (j,T)$ and $e \ne d$, the names $x$ of $e$ and $y$ of $d$ are
  scoped and $(\Delta \setminus d)[e \mapsto (k,S')] \vdash_n p$, then $\Delta \vdash_n
  \overline{x}\langle y\rangle.p$.
- Endpoint input: if $\Delta(e) = (k,S)$, $\mathrm{unf}(S) = {?(r,j,T)}.S'$, the name $x$ of $e$ is
  scoped and $\uparrow_0(\Delta[e \mapsto (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)] \vdash_{n+1} p$,
  then $\Delta \vdash_n x(\cdot).p$.
- If $\Delta$ and $\Theta$ have disjoint domains, $\Delta \vdash_n p$ and $\Theta \vdash_n q$, then
  $\Delta \cup \Theta \vdash_n p \mid q$.
- If $c$ is a capability and $\nu_c\Delta \vdash_{n+1} p$, then $\Delta \vdash_n \nu\,p$.

Here the input $x(\cdot).p$ binds $\mathrm{v}_0$ in $p$, $\uparrow_0\Delta$ adds one to the index of
every variable name of an endpoint of $\Delta$, $\nu_c\Delta$ is $\uparrow_0\Delta$ extended with
$\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$ (same rank, dual protocol), and
$\Delta \setminus d$ removes the entry of $d$. Replication and choice are not typable.
