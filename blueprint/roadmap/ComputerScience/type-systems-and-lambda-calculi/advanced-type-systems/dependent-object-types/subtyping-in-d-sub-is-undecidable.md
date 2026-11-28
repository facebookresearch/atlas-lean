# Subtyping in D<: is undecidable

No algorithm decides, given a context and two types of the calculus $D_{<:}$, whether the first type is a subtype of the second; the result holds also for the normal-form rules without the bad-bounds rule.

**Theorem.** The subtyping problem of [the calculus $D_{<:}$](the-calculus-d-sub.md) (given $\Gamma$, $S$ and $U$, is $\Gamma \vdash S <: U$ derivable?) is undecidable. It remains undecidable for the normal-form presentation of $D_{<:}$ subtyping with the bad-bounds rule removed. The normal form keeps Top, Bot, Refl, Bnd and All, replaces Sel1 and Sel2 by Sel1' (from $\Gamma \vdash \Gamma(x) <: \{A : S .. \top\}$ infer $\Gamma \vdash S <: x.A$) and Sel2' (from $\Gamma \vdash \Gamma(x) <: \{A : \bot .. U\}$ infer $\Gamma \vdash x.A <: U$), and replaces Trans by the bad-bounds rule BB (from $\Gamma \vdash \Gamma(x) <: \{A : S .. \top\}$ and $\Gamma \vdash \Gamma(x) <: \{A : \bot .. U\}$ for some $x$ infer $\Gamma \vdash S <: U$); with BB it derives exactly the judgments of the original rules.

## Depends on

- [The calculus D<:](the-calculus-d-sub.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Subtyping in full F-sub is undecidable](../subtyping-in-full-f-sub-is-undecidable.md)

## Expansion

The proof reduces subtyping in $F_{<:}^-$, which is $F_{<:}$ without function types; it is undecidable because Pierce's undecidability proof for $F_{<:}$ never uses function types. The translation of Amin and coauthors maps a type variable $X$ to $x_X.A$, a bound $X <: T$ in the context to $x_X : \{A : \bot .. \langle T \rangle\}$, and $\forall X <: S.\, U$ to $\forall(x_X : \{A : \bot .. \langle S \rangle\})\, \langle U \rangle$. If $\Gamma \vdash S <: U$ in $F_{<:}^-$ then the translated judgment holds in $D_{<:}$. For the converse a naive translation fails because of bad bounds; the source works with the normal form of $D_{<:}$ subtyping and contexts with invertible types, on which derivations translate back. The proof does not use the bad-bounds rule, hence the second statement. Earlier attempted reductions had counterexamples, which the source discusses.

## Sources

- Jason Z. S. Hu and Ondřej Lhoták, "Undecidability of $D_{<:}$ and its decidable fragments", *Proceedings of the ACM on Programming Languages* 4(POPL), 30 pages, 2020, <https://doi.org/10.1145/3371077>; read as arXiv:1908.05294v1, <https://arxiv.org/abs/1908.05294v1>: the theorems "Subtyping in $D_{<:}$ is undecidable" and "Subtyping in $D_{<:}$ normal form without the bad-bounds rule is undecidable" and their proofs, in the section "Undecidability of $D_{<:}$ (sub)typing" of that version.
