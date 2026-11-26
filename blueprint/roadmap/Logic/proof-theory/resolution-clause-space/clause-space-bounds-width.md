# Atserias–Dalmau inequality: clause space bounds width

If a CNF formula $\varphi$ whose clauses have width at most $k$ has a resolution refutation in clause space $s$, then it has a resolution refutation of width at most $s + k - 3$. Hence width lower bounds give clause space lower bounds: $\mathrm{Sp}(\varphi \vdash \bot) \ge W(\varphi \vdash \bot) - W(\varphi) + 3$.

## Proof sketch

From a small-space refutation, Spoiler obtains a strategy in the existential pebble game with $s + k - 2$ pebbles by pebbling the variables of the clauses in memory and searching for the falsified clause; by the game characterization this bounds width.

## Depends on

- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Proof depends on

- [Atserias–Dalmau: the existential pebble game characterizes resolution width](atserias-dalmau-width-characterization.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008.
- Y. Filmus, M. Lauria, M. Mikša, J. Nordström and M. Vinyals, "From Small Space to Small Width in Resolution", 31st Symposium on Theoretical Aspects of Computer Science (STACS), 2014.
