# Reductions from formulas to polynomial systems

A formula $\Gamma$ reduces to a system of polynomials over $\mathbb Z_m$ in depth $d$ and size $T$ if small constant-depth formulas, provably from $\Gamma$ by a size-$T$ depth-$d$ Frege derivation, define an $m$-partition of the satisfied monomials of every polynomial in the system.

Since only $0/1$ assignments matter, polynomials are replaced by their multilinearizations. Let $f=\sum_{I\subseteq[n]}a_Ix_I$ be a multilinear polynomial over $\mathbb Z_m$, with $x_I=\prod_{i\in I}x_i$. Its *set of monomials* is

$$
M_f=\{m_{c,I}: I\subseteq[n],\ c\in[a_I]\},
$$

so a term $a_Ix_I$ contributes $a_I$ distinct copies of $x_I$. Over $\mathbb Z_m$, $f$ vanishes at a $0/1$ assignment exactly when its satisfied monomials (copies $m_{c,I}$ with all $x_k$, $k\in I$, true) can be partitioned into blocks of size $m$.

With $[S]^m$ and the conflict relation $\perp$ as for [counting axioms modulo $m$](counting-axioms-modulo-m.md), formulas $\theta_E$ in $\vec x$, one for each $E\in[M_f]^m$, *form an $m$-partition of the satisfied monomials of $f$* if the following holds: every $\theta_E$ implies that all monomials in $E$ are satisfied; no two conflicting $E\perp F$ have $\theta_E$ and $\theta_F$ both true; and every satisfied monomial $m_{c,I}$ lies in some $E$ with $\theta_E$ true.

Let $\Gamma(\vec x)$ be a propositional formula and $F=\{f_1,\dots,f_k\}$ a system of polynomials over $\mathbb Z_m$ with a [Nullstellensatz refutation](nullstellensatz-refutations.md) $p_1,\dots,p_k,r_1,\dots,r_n$. $\Gamma$ *reduces to $F$ in depth $d$ and size $T$* if for each $i$ there are formulas $\beta^i_E(\vec x)$, $E\in[M_{\bar f_i}]^m$, and a size-$T$, depth-$d$ Frege derivation from $\Gamma$ of the statement that, for each $i$, the $\beta^i$ form an $m$-partition of the satisfied monomials of the multilinearization $\bar f_i$.

## Expansion

The definition is designed so that the usual translations of formulas into polynomials are reductions. For the *direct translation* of clauses ($tr(\emptyset)=1$, $tr(A\vee x)=tr(A)(1-x)$, $tr(A\vee\neg x)=tr(A)x$), an unsatisfiable CNF with $m$ clauses of width $w$ reduces to $tr(F)$ in depth $O(1)$ and size $m2^{O(w)}$. For a formula $f$ over $\{\bigvee,\neg\}$ and its extension-variable translation $\mathrm{POLY}(f)$, $f$ reduces to $\mathrm{POLY}(f)$ in depth $O(\mathrm{depth}(f))$ and size polynomial in $|f|$. The same idea of encoding an equation by a perfect matching on its satisfied monomials reappears in the [perfect matching encoding of the weak rank principle](../linear-algebra-in-proof-complexity/weak-rank-perfect-matching-lower-bounds.md).

## Depends on

- [Bounded-depth Frege proofs](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md)
- [Counting axioms modulo m](counting-axioms-modulo-m.md)
- [Nullstellensatz refutations](nullstellensatz-refutations.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 4 (opening); Section 4.1, Definitions 9, 10 and 11 (M_f, m-partitions of satisfied monomials and reductions); Sections 5.1 and 5.2 for the translations).
