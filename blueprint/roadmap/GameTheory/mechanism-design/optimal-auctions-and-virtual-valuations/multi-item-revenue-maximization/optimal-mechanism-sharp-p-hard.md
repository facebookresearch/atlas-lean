# Computing optimal multi-item mechanisms is #P-hard

For a single additive buyer whose values for $n$ items are independent and each supported on two rational values with rational probabilities, no expected-polynomial-time algorithm finds and implements an optimal mechanism (of any format, direct or indirect) unless $\mathrm{ZPP} \supseteq \mathrm{P}^{\#\mathrm{P}}$. Moreover, it is $\#\mathrm{P}$-hard, under the promise that one of the two cases holds for all optimal mechanisms, to decide whether every optimal mechanism gives a specific item to a specific type with probability $0$ or with probability $1$; in particular computing the allocation rule of an optimal Bayesian incentive-compatible mechanism is $\#\mathrm{P}$-hard. In contrast, for a constant number of items with finite supports the optimal mechanism is the solution of a polynomial-size linear program.

## Proof sketch

Start from the exponential-size revenue linear program over all $2^n$ types, relax it, and show that a monotone supermodular optimum of the relaxation is optimal for the original. The dual of the relaxation is a minimum-cost flow problem on the lattice of types; for a suitable class of two-point instances its canonical solution orders the types by subset sums, which pins down the unique optimal mechanism. Whether it allocates a given item to a given type then encodes the lexicographic rank of a set, a quantity as hard as counting subset sums ($\#$-SubsetSum). For constant $n$ with finite supports, the revenue-maximization linear program over all types has size polynomial in the input.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)
- [$\#P$-complete functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)

## Sources

- C. Daskalakis, A. Deckelbaum, C. Tzamos, "The Complexity of Optimal Mechanism Design", SODA 2014, arXiv:1211.1703, Theorem 1 and Corollary 1.
