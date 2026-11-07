# Cost of the Freivalds trial

For $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2$ and every seed $r \in \mathbb{F}_2^n$, the Freivalds trial performs exactly
$3n^2$ scalar multiplications and exactly $3n^2$ scalar additions.

These counts belong to the same run that returns the acceptance bit and include the additions
into the zero-initialized accumulators.
