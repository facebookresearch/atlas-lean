# The calculus D<:

$D_{<:}$ is the fragment of dependent object types with type declarations $\{A : S .. U\}$ bounded below and above, path types $x.A$ selecting the single type label $A$ of a variable, and dependent function types; its typing and subtyping rules are mutually recursive.

**Syntax.** Types and terms are

$$
S, T, U ::= \top \mid \bot \mid \{A : S .. U\} \mid x.A \mid \forall(x : S)\, U_x, \qquad v ::= \{A = T\} \mid \lambda(x : T)\, t_x, \qquad s, t, u ::= x \mid v \mid x\ y \mid \mathtt{let}\ x = t\ \mathtt{in}\ u_x,
$$

with variables $x, y, z$; contexts $\Gamma$ list typings $x : S$.

**Type assignment.** $\Gamma \vdash x : \Gamma(x)$ (Var); from $\Gamma \vdash t : S$ and $\Gamma \vdash S <: U$ infer $\Gamma \vdash t : U$ (Sub); from $\Gamma; x : S \vdash t : U_x$ infer $\Gamma \vdash \lambda(x : S)\, t : \forall(x : S)\, U_x$ (All-I); from $\Gamma \vdash x : \forall(z : S)\, U_z$ and $\Gamma \vdash y : S$ infer $\Gamma \vdash x\ y : U_y$ (All-E); $\Gamma \vdash \{A = T\} : \{A : T .. T\}$ (Typ-I); from $\Gamma \vdash t : S$, $x \notin fv(U)$ and $\Gamma; x : S \vdash u : U$ infer $\Gamma \vdash \mathtt{let}\ x = t\ \mathtt{in}\ u : U$ (Let).

**Subtyping.** $\Gamma \vdash T <: \top$ (Top); $\Gamma \vdash \bot <: T$ (Bot); $\Gamma \vdash T <: T$ (Refl); from $\Gamma \vdash S_2 <: S_1$ and $\Gamma \vdash U_1 <: U_2$ infer $\Gamma \vdash \{A : S_1 .. U_1\} <: \{A : S_2 .. U_2\}$ (Bnd); from $\Gamma \vdash S_2 <: S_1$ and $\Gamma; x : S_2 \vdash U_1 <: U_2$ infer $\Gamma \vdash \forall(x : S_1)\, U_1 <: \forall(x : S_2)\, U_2$ (All); from $\Gamma \vdash x : \{A : S .. U\}$ infer $\Gamma \vdash S <: x.A$ (Sel1) and $\Gamma \vdash x.A <: U$ (Sel2); from $\Gamma \vdash S <: T$ and $\Gamma \vdash T <: U$ infer $\Gamma \vdash S <: U$ (Trans).

The subtyping problem asks, given $\Gamma$, $S$ and $U$, whether $\Gamma \vdash S <: U$ is derivable; the typing problem asks, given $\Gamma$, $t$ and $T$, whether $\Gamma \vdash t : T$ is derivable.

## Depends on

None.

## Proof depends on

None.

## Expansion

Through Sel1, Sel2 and Trans a variable whose type has bounds $\{A : S .. U\}$ makes $S <: x.A <: U$, so $S <: U$ even when the bounds are unrelated (bad bounds); this is what makes transitivity hard to eliminate. The source gives an equivalent normal form of the subtyping rules without Trans, in which bad bounds become one explicit rule, and identifies decidable fragments without that rule (kernel and strong kernel $D_{<:}$).

## Sources

- Jason Z. S. Hu and Ondřej Lhoták, "Undecidability of $D_{<:}$ and its decidable fragments", *Proceedings of the ACM on Programming Languages* 4(POPL), 30 pages, 2020, <https://doi.org/10.1145/3371077>; read as arXiv:1908.05294v1, <https://arxiv.org/abs/1908.05294v1>: the definition of $D_{<:}$ (the figure "Definition of $D_{<:}$" and the definition that follows it), in the section "Definitions of $F_{<:}$ and $D_{<:}$" of that version, after Amin, Grütter, Odersky, Rompf and Stucki.
