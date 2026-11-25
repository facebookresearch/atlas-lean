# Top trading cycles for housing markets

In a housing market with $n$ agents, each owning one house and having strict preferences over all houses, the top
trading cycles algorithm (each agent points to the owner of its favorite remaining house; agents on cycles trade and
leave; repeat) terminates after at most $n$ rounds. Its output is the unique strict-core allocation (Roth and
Postlewaite). The mechanism that selects it (the Core mechanism) is strategyproof, and it is the only mechanism for
housing markets that is Pareto optimal, individually rational and strategyproof (Ma). Here a mechanism maps each
profile of reported strict preferences to an allocation, with no monetary transfers, and strategyproof means
dominant-strategy incentive compatible when each agent's type is its strict preference order and its utility for an
allocation is $U_i$ of the house it receives, for any function $U_i$ that represents its true order on houses
($U_i(h) > U_i(h')$ exactly when it prefers $h$ to $h'$). Equivalently, no agent obtains a house it strictly prefers by
misreporting, whatever the others report; this does not depend on the representing functions chosen.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Shapley-Scarf housing markets.

## Depends on

- [Dominant-strategy incentive compatibility](../../mechanism-design/revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Sources

- F. Brandt, V. Conitzer, U. Endriss, J. Lang and A. D. Procaccia (eds.), *Handbook of Computational Social Choice*, Cambridge University Press, 2016, §14.3 (the top trading cycles algorithm and the result of Roth and Postlewaite), Theorem 14.16 (Roth, 1982) and Theorem 14.17 (Ma, 1994). <https://www.cse.unsw.edu.au/~haziz/comsoc.pdf>
