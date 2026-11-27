# Visible edge of a protocol tree after root unrolling

The edge relation $S \xrightarrow{\ell} T$ between protocols is defined from the head
$\mathrm{unf}(S)$ of $S$ (its first action or $\mathrm{end}$, a graph cursor being unrolled once):

- if $\mathrm{unf}(S) = {!\mathrm{N}}.T$ then $S \xrightarrow{!\mathrm{N}} T$, and if
  $\mathrm{unf}(S) = {?\mathrm{N}}.T$ then $S \xrightarrow{?\mathrm{N}} T$;
- if $\mathrm{unf}(S) = {!(r,k,P)}.T$ then $S \xrightarrow{!(r,k,\mathrm{pay})} P$ and $S
  \xrightarrow{!(r,k,\mathrm{cont})} T$;
- if $\mathrm{unf}(S) = {?(r,k,P)}.T$ then $S \xrightarrow{?(r,k,\mathrm{pay})} P$ and $S
  \xrightarrow{?(r,k,\mathrm{cont})} T$.

There are no other edges; in particular a protocol with head $\mathrm{end}$ has none.
