# Closed normal forms of System T

Write $\to_T$ for one-step reduction of [Gödel's System T](godel-s-system-t.md) in its presentation with the constants $0$, $\mathrm{S}$ and $\mathrm{R}_A$: β-reduction together with the recursor rules $\mathrm{R}\,u\,v\,0 \to u$ and $\mathrm{R}\,u\,v\,(\mathrm{S}\,t) \to v\,t\,(\mathrm{R}\,u\,v\,t)$, in any context; $=_T$ for the convertibility it generates; and $\underline{n} = \mathrm{S}^n\,0$ for the numerals. Let $M$ be a closed term of System T in normal form with $\vdash M : \tau$.

1. If $\tau = \mathrm{nat}$, then $M = \underline{n}$ for some $n \in \mathbb{N}$.
2. If $\tau = \tau_1 \to \tau_2$, then $M$ is an abstraction $\lambda x.\, N$, or a constant or partially applied recursor of that type ($\mathrm{S}$, $\mathrm{R}_A$, $\mathrm{R}_A\, u$ or
   $\mathrm{R}_A\, u\, v$ with $u$, $v$ normal).

With strong normalization, every closed term of type $\mathrm{nat}$ reduces to a unique numeral.

## Depends on

- [Gödel's System T](godel-s-system-t.md)

## Proof depends on

- [Strong normalization of System T](strong-normalization-of-system-t.md)
- [Church–Rosser property of System T](church-rosser-property-of-system-t.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Proposition 11.6.6, stated there for the presentation with the recursor $\mathrm{r}(M, N, L)$ as a term former, where a closed normal term of function type is an abstraction; with the recursor as a constant, as in the definition linked above, the same induction on normal forms gives the constant and partial-application cases.
