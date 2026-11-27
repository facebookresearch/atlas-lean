# Kreisel's theorem on provably total functions

A recursive function is provably total in Peano arithmetic if and only if it is provably total in [Heyting arithmetic](heyting-arithmetic.md): for a primitive recursive
$t_f$, $\mathrm{PA} \vdash \forall x\, \exists y\, t_f(x, y) = 0$ exactly when $\mathrm{HA} \vdash \forall x\, \exists y\, t_f(x, y) = 0$. The same holds for every sentence $\forall x\, \exists y\, R(x, y)$
with $R$ primitive recursive, and in particular, taking $R$ to be $\bot$, HA is consistent if and only if PA is.

The nontrivial direction applies the negative translation. Translating a PA derivation gives an intuitionistic derivation from the translated axioms, and these
are theorems of HA: the translation of a quantifier-free axiom is equivalent to it because equality of numbers is decidable in HA, and the translation of an
instance of induction is an instance of induction for the translated formula. This gives $\mathrm{HA} \vdash \neg\neg \exists y\, t_f(x, y) = 0$ with $x$ free, and the proof then
removes the double negation uniformly in $x$, by Markov's rule with parameters for the decidable formula $t_f(x, y) = 0$. The closed Markov rule gives only
$\mathrm{HA} \vdash \exists y\, t_f(\underline{n}, y) = 0$ for each numeral $n$ separately; the rule with parameters has a syntactic proof by Friedman's translation.

## Depends on

- [Heyting arithmetic](heyting-arithmetic.md)
- [Provably total functions of Peano arithmetic](../../../ComputerScience/type-systems-and-lambda-calculi/system-t/provably-total-functions-of-peano-arithmetic.md)

## Proof depends on

- [Basic properties of Heyting arithmetic](basic-properties-of-heyting-arithmetic.md)
- [Gödel–Gentzen negative translation](../goedel-gentzen-negative-translation.md)

## Expansion

This page becomes ready once:

- Markov's rule with parameters for HA: if $\mathrm{HA} \vdash \forall x\, \neg\neg \exists y\, R(x, y)$ with $R$ primitive recursive, then $\mathrm{HA} \vdash \forall x\, \exists y\, R(x, y)$, proved by Friedman's translation (proof prerequisite; not yet stated)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 11.4.2 (Kreisel, 1958) with its proof, the remark after it, and Corollary 11.4.3.
- J. Avigad and S. Feferman, "Gödel's functional (“Dialectica”) interpretation", in S. R. Buss (ed.), *Handbook of Proof Theory*, Studies in Logic and the Foundations of Mathematics 137, Elsevier, 1998, pp. 337–405, <https://doi.org/10.1016/S0049-237X(98)80020-7>: Theorem 2.1.1, Corollary 2.1.2 and its proof 2.1.3 (the negative translation of PA derivations into HA).
