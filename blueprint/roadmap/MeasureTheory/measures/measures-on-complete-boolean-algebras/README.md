# Von Neumann's conditions do not guarantee a measure

There is a complete Boolean algebra that satisfies the countable chain condition and von Neumann's
generalized distributivity law but carries no measure in von Neumann's sense: no real-valued,
countably additive $\mu$ with $\mu(\bot) = 0$ and $\mu(a) > 0$ for every $a \ne \bot$. This answers
Problem 163 of the Scottish Book in the negative, in its stated form.

## Idea

The measurable sets of a probability space modulo null sets form a complete Boolean algebra
carrying a strictly positive measure. Such an algebra satisfies the countable chain condition, since
a disjoint family of elements of positive measure is countable, and von Neumann's distributivity
law. Von Neumann asked whether these two conditions characterise the algebras that carry a measure.
Maharam isolated a sub-question: whether every such algebra that carries a well-behaved
(continuous) submeasure also carries a measure. Talagrand answered it in the negative by
constructing an exhaustive submeasure equivalent to no measure; the algebra it gives satisfies both
of von Neumann's conditions but carries no measure, which yields the counterexample.

## Statements

- [Von Neumann's conditions do not guarantee a measure](von-neumann-conditions-not-sufficient.md)
- [Von Neumann's sufficiency claim](von-neumann-sufficiency-claim.md): the claim as a proposition.
- [Von Neumann measures on a complete Boolean algebra](is-von-neumann-measure.md): a definition used in the claim.
- [The countable chain condition for complete Boolean algebras](satisfies-countable-chain-condition.md): a definition used in the claim.
- [Von Neumann's generalized distributivity law](satisfies-generalized-distributivity.md): a definition used in the claim.

## Sources

- J. von Neumann, Problem 163 of the Scottish Book; see R. D. Mauldin (ed.), *The Scottish Book*, 2nd ed., Birkhäuser, 2015.
- M. Talagrand, *Maharam's problem*, arXiv:math/0601689 (2006).
