# DCJ breakpoint cycles versus random transpositions

Use the mechanistic DCJ model of expected breakpoints after random DCJ operations: a genome is a perfect matching of $n$ adjacencies (observed, telomeric and fictional), evolving by uniformly random DCJs. The **breakpoint graph** of $G$ and $G_k$ is the union of their adjacencies, a disjoint union of alternating cycles; the **real** breakpoint graph uses the telomere correspondence inherited from the evolutionary process, and the **observed** one closes the paths of observed adjacencies with telomeric and fictional elements so as to maximize the number of cycles; the two cycle counts differ by $o(n)$.

**Theorem.** Let $BCy_k$ be the number of cycles of the breakpoint graph between $G$ and $G_k$ obtained by $k$ random DCJs, and $Cy_k$ the number of cycles of a permutation of $n$ elements obtained from the identity by $k$ uniformly random transpositions. Then

$$\mathbb E[BCy_k] = \mathbb E[Cy_k] + o(n),$$

for the real and the observed breakpoint graph alike. More precisely $\mathbb E[BCy_k] \le \mathbb E[Cy_k] \le \mathbb E[BCy_k] + O(k/n)$ in the relevant range, and only $k = O(n \log n)$ is informative before saturation, so the error is $o(n)$.

Combined with Berestycki and Durrett's comparison of $\mathbb E[Cy_k]$ with the expected number $\mathbb E[Co_k]$ of components after adding $k$ random edges to $n$ isolated vertices (equal up to a lower-order term), the exact Eriksen–Hultman formula for $\mathbb E[Cy_k]$ and random-graph tree counts both estimate DCJ cycle counts, hence DCJ distances, with error $o(n)$.

## Depends on

- [Expected breakpoints after random DCJ operations](expected-breakpoints-after-random-dcj-operations.md)
- [Number of cycles of a permutation](../../../Combinatorics/stirling-bell-eulerian/stirling-lah-numbers/stirling-numbers-of-the-first-kind/cycle-quotient-count.md)

## Expansion

Couple the processes by identifying adjacencies with permutation elements and applying the transposition $(a\,b)$ whenever the DCJ cuts adjacencies $a, b$. If $a, b$ lie in different breakpoint cycles both processes fuse two cycles. If they lie in one cycle, the transposition always splits it, while the DCJ splits it with probability $1/2$ and otherwise only reorders it; hence breakpoint cycles never outnumber permutation cycles. The discrepancy comes only from the non-splitting DCJ moves; a cycle of a given small size is created by such a move with probability of order $1/n$ per step, while large cycles are few, which bounds the expected gap after $k$ steps by $O(k/n)$. DCJ is thus a coagulation–fragmentation–nothing process sandwiched between random transpositions (coagulation–fragmentation) and random graphs (coagulation–nothing).

## Sources

- P. Biller, L. Guéguen, E. Tannier, "Moments of genome evolution by Double Cut-and-Join", BMC Bioinformatics 16 (Suppl 14) (2015) S7, sections "Breakpoint graphs", Theorem 2 and its proof, Theorem 3 (after Berestycki–Durrett) and the Corollary, <https://doi.org/10.1186/1471-2105-16-S14-S7>, PMCID PMC4602343.
