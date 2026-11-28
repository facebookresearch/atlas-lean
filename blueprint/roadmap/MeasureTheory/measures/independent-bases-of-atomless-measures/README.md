# Szpilrajn's Problem 191

Not every convex measure has a base. There are a measurable space $X$ and a probability measure
$\mu$ on $X$ such that every measurable set of positive measure contains a measurable subset of
strictly smaller positive measure, but no class $B$ of measurable sets is a base of $\mu$, that
is, stochastically independent for $\mu$ and generating every measurable set up to a null set.

## Idea

For Lebesgue measure on $[0, 1]$, the sets of numbers whose $n$-th binary digit is $1$ form a base:
they are independent fair coin tosses, and together they determine every measurable set up to a
null set. Szpilrajn asked whether every atomless probability measure has such a base. Maharam's
theorem answers it: an atomless measure has a base exactly when its measure algebra is
homogeneous, isomorphic to that of coin tossing on $\{0, 1\}^\kappa$ for one cardinal $\kappa$.
Mixing, with weights $\frac12$, Lebesgue measure on $[0, 1]$ and coin tossing on $\{0, 1\}^I$ for
an uncountable set $I$ gives an algebra that is not homogeneous, hence a measure without a base.

## Statements

- [Szpilrajn's Problem 191 has a negative answer](szpilrajn191-refuted.md)
- [The claim of Szpilrajn's Problem 191](scottish-book-problem191-claim.md): the claim as a proposition.
- [Base of a measure](is-base.md): a definition used in the claim.
- [Convex measure](is-convex-measure.md): a definition used in the claim.
- [Stochastically independent class of sets](is-independent-class.md): a definition used in the claim.

## Sources

- E. Szpilrajn, Problem 191 of the Scottish Book; see R. D. Mauldin (ed.), *The Scottish Book*, 2nd ed., Birkhäuser, 2015.
- D. Maharam, *On homogeneous measure algebras*, Proc. Nat. Acad. Sci. U.S.A. 28 (1942).
