# Computing optimal multi-item mechanisms is #P-hard

For a single additive buyer whose values for $n$ items are independent and each supported on two values $\{a_j, b_j\}$, it is $\#\mathrm{P}$-hard to determine whether the optimal mechanism is to sell the grand bundle at a single price; hence computing the optimal mechanism (for instance its allocation probabilities at a given type) is $\#\mathrm{P}$-hard even for this simple class. In contrast, for a constant number of items with finite supports the optimal mechanism is the solution of a polynomial-size linear program.

## Proof sketch

Use the duality between optimal mechanisms and optimal transport: for two-point distributions the optimality of grand bundling is certified by a transport plan whose existence reduces to a counting condition on subsets of items, equivalent to a subset-sum counting problem. For constant $n$ with finite supports, the revenue-maximization linear program over all types has size polynomial in the input.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Strong duality between optimal mechanisms and optimal transport for a single additive buyer](strong-duality-multiple-good-monopolist.md)

## Sources

- C. Daskalakis, A. Deckelbaum, C. Tzamos, "The Complexity of Optimal Mechanism Design", SODA 2014, arXiv:1211.1703.
