# A separable stably finite algebra without tracial states

There exists a nonzero separable unital complex $C^*$-algebra in which every isometry in every positive-size matrix algebra is unitary, but on which no positive complex-linear functional is at once normalized by $\tau(1)=1$ and tracial, meaning $\tau(ab)=\tau(ba)$ for all $a,b$. This clause neither assumes simplicity nor claims absence of normalized two-quasitraces.

## Depends on
Matrix-level stable finiteness and positive linear tracial states on the same unital algebra.

## Proof depends on

The finite column/row obstruction to a normalized trace and stable finiteness of the faithful dimension-state quotient, together with separable extraction.

## Expansion

Separate the finite tuple certificate (column sum the unit and row sum strictly below the unit) from its tracial obstruction. Transfer the obstruction by pulling tracial states back along the quotient map, and then verify the separable extraction retains the obstruction and all positive-size matrix finiteness conditions.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KaplanskyStableFiniteness.lean#L240-L242) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/294.md).
