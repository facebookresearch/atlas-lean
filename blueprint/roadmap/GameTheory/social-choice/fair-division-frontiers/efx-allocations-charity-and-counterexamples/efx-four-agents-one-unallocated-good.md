# EFX for four additive agents with at most one unallocated good

For every instance with four agents having additive valuations there is a partial EFX allocation leaving at most one good unallocated, with no agent envying the unallocated good. For every $n \ge 2$ and additive valuations there is a partial EFX allocation leaving at most $n - 2$ goods unallocated, again with no agent envying the pool. Both statements extend to the class of nice cancelable valuations, which contains additive, unit-demand and budget-additive valuations.

## Proof sketch

Introduce a refined potential combining the lexicographic valuation vector with the structure of the envy graph and the champion relations, and show that if two or more goods remain in the pool (for four agents), or $n - 1$ or more (in general), some local reallocation along champion paths strictly improves the potential while maintaining EFX. Cancelability (the property $v(S \cup \{g\}) > v(T \cup \{g\}) \Rightarrow v(S) > v(T)$) is the only property of additivity the case analysis uses.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Proof depends on

- [EFX with bounded charity: fewer than n goods left unallocated](efx-with-bounded-charity.md)
- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)

## Sources

- B. Berger, A. Cohen, M. Feldman, A. Fiat, "Almost Full EFX Exists for Four Agents", AAAI 2022, arXiv:2102.10654.
