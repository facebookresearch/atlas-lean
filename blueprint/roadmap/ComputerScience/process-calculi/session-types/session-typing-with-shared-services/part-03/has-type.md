# Runtime typing with guarded shared replication

Runtime typing $\Gamma; \Delta \vdash_n p$ relates a natural number $n$ (binder depth), a service
environment $\Gamma$, an ownership context $\Delta$ and a process $p$. It is defined inductively by
ten rules. Throughout, $\mathrm{unf}(S)$ is the head of $S$, "scoped" means scoped at depth $n$,
$\mathrm{Min}_\Delta(e,k)$ means that every endpoint $d \ne e$ with an active capability in $\Delta$
has rank $> k$, and $\Gamma \perp \Delta$ means that no endpoint owned by $\Delta$ is named by a
declared trigger $\mathrm{c}_s$.

- Nil: if every capability of $\Delta$ has head $\mathrm{end}$, every endpoint of $\Delta$ is scoped
  and $\Gamma \perp \Delta$, then $\Gamma; \Delta \vdash_n \mathbf{0}$.
- Passive output: if $\mathrm{Min}_\Delta(e,k)$, $\Gamma \perp \Delta$, $\Delta(e) = (k,S)$,
  $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, the name $x$ of $e$ and $b$ are scoped and $\Gamma; \Delta[e
  \mapsto (k,S')] \vdash_n p$, then $\Gamma; \Delta \vdash_n \overline{x}\langle b\rangle.p$.
- Passive input: if $\mathrm{Min}_\Delta(e,k)$, $\Gamma \perp \Delta$, $\Delta(e) = (k,S)$,
  $\mathrm{unf}(S) = {?\mathrm{N}}.S'$, $x$ is scoped and $\Gamma; \uparrow_0(\Delta[e \mapsto
  (k,S')]) \vdash_{n+1} p$, then $\Gamma; \Delta \vdash_n x(\cdot).p$.
- Endpoint output: if $\mathrm{Min}_\Delta(e,k)$, $\Gamma \perp \Delta$, $\Delta(e) = (k,S)$,
  $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $d$ has polarity $r$, $\Delta(d) = v \approx (j,T)$, $e \ne d$,
  the names $x$ of $e$ and $y$ of $d$ are scoped and $\Gamma; (\Delta \setminus d)[e \mapsto (k,S')]
  \vdash_n p$, then $\Gamma; \Delta \vdash_n \overline{x}\langle y\rangle.p$.
- Endpoint input: if $\mathrm{Min}_\Delta(e,k)$, $\Gamma \perp \Delta$, $\Delta(e) = (k,S)$,
  $\mathrm{unf}(S) = {?(r,j,T)}.S'$, $x$ is scoped and $\Gamma; \uparrow_0(\Delta[e \mapsto
  (k,S')])[\mathrm{v}_0^{r} \mapsto (j,T)] \vdash_{n+1} p$, then $\Gamma; \Delta \vdash_n
  x(\cdot).p$.
- Invocation: if $\Gamma(s) = (\pi, r, c)$, $\Gamma \perp \Delta$, $\Delta(e) = v$, $e$ has polarity
  $r$, $v \approx c$, $\pi$ is below the rank of every active capability of $\Delta$, the name $y$
  of $e$ is scoped and $\Gamma; \Delta \setminus e \vdash_n p$, then $\Gamma; \Delta \vdash_n
  \overline{\mathrm{c}_s}\langle y\rangle.p$.
- Accept: if $\Gamma(s) = (\pi, r, c)$, every capability of $\Delta$ has head $\mathrm{end}$, every
  endpoint of $\Delta$ is scoped, $\Gamma \perp \Delta$ and $\Gamma; \{\mathrm{v}_0^{r} \mapsto c\}
  \vdash_{n+1} p$, then $\Gamma; \Delta \vdash_n \mathrm{c}_s(\cdot).p$.
- Serve: if $p$ is a service template for $\Gamma$, $\Gamma; \emptyset \vdash_n p$, every capability
  of $\Delta$ has head $\mathrm{end}$, every endpoint of $\Delta$ is scoped and $\Gamma \perp
  \Delta$, then $\Gamma; \Delta \vdash_n {!p}$.
- Parallel: if $\Delta$, $\Theta$ have disjoint domains, $\Gamma; \Delta \vdash_n p$ and $\Gamma;
  \Theta \vdash_n q$, then $\Gamma; \Delta \cup \Theta \vdash_n p \mid q$.
- Restriction: if $\Gamma \perp \Delta$ and $\Gamma; \nu_c\Delta \vdash_{n+1} p$ for a capability
  $c$, then $\Gamma; \Delta \vdash_n \nu\,p$.

Here $\approx$ is capability equivalence (equal ranks, tree-equivalent protocols), $\uparrow_0$
raises every variable name index of an endpoint by one, $\nu_c\Delta$ is $\uparrow_0\Delta$ extended
by $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$, and a service template is
built from $\mathbf{0}$ and inputs on declared triggers by $\mid$, $\nu$ and replication.
