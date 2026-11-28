# k-break distances and lower bounds on breakpoint reuse

**Setting.** A circular genome $P$ on $n = |P|$ synteny blocks is represented by its *black* edges (adjacencies between block extremities); comparing $P$ with $Q$ on the same blocks gives the *breakpoint graph* $G(P,Q)$, whose edges are the black adjacencies of $P$ and the gray adjacencies of $Q$, decomposing into alternating black-gray cycles. A *$k$-break* cuts $k$ adjacencies of a genome and rejoins the $2k$ freed extremities in a new way; a 2-break models reversals, translocations, fusions and fissions, while a 3-break also models transpositions. A $k$-break is *complete* if it actually breaks $k$ adjacencies (a 3-break that breaks only two is a 2-break). The $k$-break distance $d_k(P,Q)$ is the minimum number of $k$-breaks transforming $P$ into $Q$; $c(P,Q)$ is the number of black-gray cycles and $c_{odd}(P,Q)$ the number with an odd number of black edges.

**Theorems.**

1. $d_2(P,Q) = |P| - c(P,Q)$.
2. $d_3(P,Q) = \bigl(|P| - c_{odd}(P,Q)\bigr)/2$.
3. *Breaks bound.* Any series of $m$ $k$-breaks transforming $P$ into $Q$ makes at least $m + d_2(P,Q)$ breaks; some series of $d_3(P,Q)$ 3-breaks makes exactly $d_3(P,Q) + d_2(P,Q)$ breaks.
4. *Complete 3-breaks.* A series of $m$ 3-breaks with $t$ complete 3-breaks transforming $P$ into $Q$ has $m \ge \max\{d_2(P,Q) - t,\ d_3(P,Q)\}$, and this is attained with at most $t$ complete 3-breaks. Hence such a series makes at least $d_2(P,Q) + \max\{d_2(P,Q) - t, d_3(P,Q)\}$ breaks, and at least $2 d_2(P,Q) - t$ breaks when $t \le d_2(P,Q) - d_3(P,Q)$.

**Consequence for breakpoint reuse.** If the genomes differ at $b$ breakpoints, any rearrangement history reuses breakpoints at least (number of breaks) $- b$ times. For circularized human and mouse genomes on 281 synteny blocks, $d_2 = 246$ and $d_3 = 139$, so every 3-break scenario makes at least $385$ breaks and at least $104$ breakpoint reuses (reuse rate at least $385/281 \approx 1.37$), even allowing transpositions. Simulations of the random breakage model never reached this rate, supporting rearrangement hotspots.

## Depends on

- [Double-cut-and-join distance formula](double-cut-and-join-distance-formula.md)

## Expansion

A 2-break removes two black edges and adds two, so it changes the number of black-gray cycles by at most one, and every nontrivial cycle can be split by some 2-break; the identity graph has $|P|$ trivial cycles, giving Theorem 1 (the circular-genome case of the double-cut-and-join distance). A 3-break can raise the number of odd cycles by at most two (splitting an odd cycle into three odd ones, or an even cycle into two odd ones), and the target has $|P|$ odd cycles, giving Theorem 2. For the breaks bound, a single operation that makes $\beta$ breaks raises the cycle count by at most $\beta - 1$; summing over $m$ operations, $|P| - c(P,Q) \le (\text{breaks}) - m$. The counting in Theorem 4 trades complete 3-breaks against 2-breaks: each complete 3-break can do the work of at most two 2-breaks in cycle count. The bound is robust to the "transpositions cause apparent reuse" objection because it holds for every series of 3-breaks.

## Sources

- M. A. Alekseyev, P. A. Pevzner, "Are there rearrangement hotspots in the human genome?", PLoS Computational Biology (2007), Theorems 1–2 (2-break and 3-break distances), Theorem 4 and Corollary 5 (breaks lower bound and human–mouse breakpoint reuse), Theorem 6 and Corollary 7 (complete 3-breaks), simulations of the random breakage model (Figure 7). <https://doi.org/10.1371/journal.pcbi.0030209> (PMC2065889).
