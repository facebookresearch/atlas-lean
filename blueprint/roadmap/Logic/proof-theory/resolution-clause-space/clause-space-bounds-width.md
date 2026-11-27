# Atserias–Dalmau inequality: clause space bounds width

If a CNF formula $\varphi$ that does not contain the empty clause and whose clauses have width at most $k$ has a resolution refutation in clause space $s$, then it has a resolution refutation of width at most $s + k - 3$. Hence width lower bounds give clause space lower bounds: $\mathrm{Sp}(\varphi \vdash \bot) \ge W(\varphi \vdash \bot) - W(\varphi) + 3$.

## Proof sketch

Filmus et al. negate the configurations of the space-$s$ refutation one by one, rewrite each negation as a set of clauses of width at most $s$, list these sets in reverse order, and fill the gaps between consecutive sets by resolution steps of width at most $s + k - 3$. Atserias and Dalmau's original argument, through the existential pebble game, gives the slightly weaker $s + k - 1$.

## Depends on

- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008: Lemma 4 and Theorem 3.
- Y. Filmus, M. Lauria, M. Mikša, J. Nordström and M. Vinyals, "From Small Space to Small Width in Resolution", 31st Symposium on Theoretical Aspects of Computer Science (STACS), 2014 (expanded version arXiv:1409.2978): Theorem 3.1.
