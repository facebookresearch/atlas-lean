# Replace-one differential privacy implies add/remove differential privacy for databases with null records

Let $U$ be a set and let $\bot$ be a null value that is not in $U$. Fix a number of slots $n$, privacy parameters $\varepsilon \ge 0$ and $\delta \ge 0$, and consider padded databases $S : \{1, \dots, n\} \to U \cup \{\bot\}$. Each padded database represents the records in its non-null slots.

Call two padded databases *add/remove neighbours* if they differ in exactly one slot and that slot holds $\bot$ in one of them. Such a pair represents the removal or addition of one record.

If a mechanism $M$ on padded databases is $(\varepsilon, \delta)$-differentially private with respect to neighbouring row databases (databases that differ in at most one slot), then $M$ is $(\varepsilon, \delta)$-differentially private with respect to add/remove neighbours, with the same $\varepsilon$ and $\delta$.

The statement needs the null value. It concerns only the slot-level relation defined above, not arbitrary representations of unordered record collections. Reordering records can change several slots; passing to unordered collections requires an additional alignment or slot-symmetry argument. The conversion is available only when the mechanism's input domain accepts $\bot$ as a record; a mechanism defined only on $U$-valued rows of fixed length has no add/remove neighbours to which it applies.

## Proof sketch

Add/remove neighbours differ in exactly one slot, so they are neighbouring row databases. The privacy inequality for the larger relation therefore holds for every add/remove pair.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

No further prerequisites: the proof uses only the two neighbouring relations and the definition of differential privacy, both linked above.

## Sources

- T. Steinke, "Composition of Differential Privacy & Privacy Amplification by Subsampling", arXiv:2210.00597v4 (2022), Section 6.2: a removal or addition can be simulated by replacing the record with a null value $\bot$, so DP with respect to replacement entails DP with respect to addition or removal with the same parameters, unless the semantics of the algorithm forbids null values.
