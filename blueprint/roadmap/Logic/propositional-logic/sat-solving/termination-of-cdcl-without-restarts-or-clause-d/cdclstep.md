# Steps of CDCL without restarts or clause deletion

Let $F$ be a CNF formula. A step for $F$ from a [state](cdclstate.md) $(t, \mathcal{L})$, a trail $t$ and a finite set $\mathcal{L}$ of learned clauses, is one of:

- **decide**: add a literal $\ell$ to the front of $t$, when neither $\ell$ nor its complement is on $t$;
- **learn**: add to $\mathcal{L}$ a clause $C \notin \mathcal{L}$ [implied by](implied-by.md) $F$, possibly a clause of $F$, and move to any suffix of $t$.
