# Inversion of endpoint typing for output

Let $n$ be a natural number, $\Delta$ an ownership context, $a$, $b$ names and $p$ a process with
$\Delta \vdash_n \overline{a}\langle b\rangle.p$. Then there are an endpoint $e$ with name $a$ and a
capability $c = (k,S)$ with $\Delta(e) = c$ such that either

- $\mathrm{unf}(S) = {!\mathrm{N}}.S'$ and $\Delta[e \mapsto (k,S')] \vdash_n p$ for some protocol
  $S'$, or
- there are an endpoint $d$ with name $b$ and polarity $r$, a rank $j$ and protocols $T$, $S'$ with
  $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\Delta(d) = (j,T)$, $e \ne d$ and $(\Delta \setminus d)[e
  \mapsto (k,S')] \vdash_n p$.
