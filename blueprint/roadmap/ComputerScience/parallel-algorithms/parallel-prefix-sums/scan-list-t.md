# Timed Kogge–Stone list scan

Let $M$ be a monoid (not necessarily commutative). A *timed computation* returns a value together with a cost pair $(w, r) \in \mathbb{N} \times \mathbb{N}$; a tick adds a given pair, sequencing adds the costs componentwise, and returning a value costs $(0, 0)$. Here $w$ counts monoid multiplications (work) and $r$ counts scheduled parallel rounds; list traversal, indexing, allocation, copying and recursive calls cost nothing.

For $K \in \mathbb{N}$ and a list $y$ in $M$, the timed scan with $K$ rounds is defined by recursion on $K$: with $0$ rounds it returns $y$ at cost $(0, 0)$; with $K + 1$ rounds it runs the timed scan with $K$ rounds and then the timed round $K$ on its result. All $K$ rounds are executed even on short or empty inputs.

## Sources

- P. M. Kogge and H. S. Stone, *A parallel algorithm for the efficient solution of a general class of recurrence equations*, IEEE Transactions on Computers, 1973.
- W. D. Hillis and G. L. Steele, *Data parallel algorithms*, Communications of the ACM, 1986.
