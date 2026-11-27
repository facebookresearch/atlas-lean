# Rate matrix of the two-locus coalescent

For a real number $\rho$, the rate matrix $Q_\rho$ on the [two-locus states](two-locus-state.md) has the nonzero entries

- from linked: $-(1 + \rho)$ on the diagonal, $\rho$ to partly split, $1$ to both coalesced;
- from partly split: $1$ to linked, $-(3 + \rho/2)$ on the diagonal, $\rho/2$ to split, $1$ to $A$ coalesced, $1$ to $B$ coalesced;
- from split: $4$ to partly split, $-6$ on the diagonal, $1$ to $A$ coalesced, $1$ to $B$ coalesced;
- from $A$ coalesced: $-1$ on the diagonal, $1$ to both coalesced; from $B$ coalesced: $-1$ on the diagonal, $1$ to both coalesced;

and all its other entries, including the whole row of "both coalesced", are $0$. For $\rho \ge 0$ it is the rate matrix of the two-locus ancestral process of a sample of two, with time in units of $2N$ generations and $\rho = 4Nr$: every pair of ancestral lineages coalesces at rate $1$ and every lineage ancestral at both loci recombines at rate $\rho/2$.
