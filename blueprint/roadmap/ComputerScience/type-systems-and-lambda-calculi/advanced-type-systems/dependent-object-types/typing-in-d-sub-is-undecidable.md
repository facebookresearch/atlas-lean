# Typing in D<: is undecidable

No algorithm decides, given a context, a term and a type of the calculus $D_{<:}$, whether the term has that type; the proof cannot go through subtyping directly, because bad bounds break inversion.

**Theorem.** The typing problem of [the calculus $D_{<:}$](the-calculus-d-sub.md) (given $\Gamma$, $t$ and $T$, is $\Gamma \vdash t : T$ derivable?) is undecidable.

## Depends on

- [The calculus D<:](the-calculus-d-sub.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Subtyping in full F-sub is undecidable](../subtyping-in-full-f-sub-is-undecidable.md)

## Expansion

The proof reduces $F_{<:}^-$ subtyping, as for [subtyping in $D_{<:}$](subtyping-in-d-sub-is-undecidable.md): $\Gamma \vdash S <: U$ in $F_{<:}^-$ is mapped to the typing problem $\langle \Gamma \rangle \vdash \{A = \langle S \rangle\} : \{A : \bot .. \langle U \rangle\}$. Only Typ-I and Sub apply to the type tag, so a derivation gives $\{A : \langle S \rangle .. \langle S \rangle\} <: \{A : \bot .. \langle U \rangle\}$ in an invertible context, hence $\langle S \rangle <: \langle U \rangle$ and $S <: U$. In general $D_{<:}$ typing does not reduce to $D_{<:}$ subtyping in this way, since with bad bounds $\{A = S\}$ can have type $\{A : \bot .. U\}$ although $S <: U$ fails.

## Sources

- Jason Z. S. Hu and Ondřej Lhoták, "Undecidability of $D_{<:}$ and its decidable fragments", *Proceedings of the ACM on Programming Languages* 4(POPL), 30 pages, 2020, <https://doi.org/10.1145/3371077>; read as arXiv:1908.05294v1, <https://arxiv.org/abs/1908.05294v1>: the theorems "$D_{<:}$ typing is undecidable" and the preceding implication from typing of type tags to $F_{<:}^-$ subtyping, in the section "Undecidability of $D_{<:}$ (sub)typing" of that version.
