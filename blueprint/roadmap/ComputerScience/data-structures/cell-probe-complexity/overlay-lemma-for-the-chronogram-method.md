# Overlay lemma for the chronogram method

In the setting of chronogram epochs, suppose every operation probes at most $d$ cells. Then:

1. the overlay memory $\widetilde{m}_j$ agrees with the true final memory outside $\mathrm{Last}_j$;
2. $\widetilde{m}_j$ differs from the memory before epoch $j$ in at most $|\mathrm{Later}_j| \le d \sum_{k > j} |\mathrm{seg}_k|$ cells;
3. the sets $\mathrm{Last}_0, \dots, \mathrm{Last}_{L-1}$ are pairwise disjoint, so a query probing $p$ cells meets at most $p$ of them;
4. a query whose probed cells avoid $\mathrm{Last}_j$ returns the same answer on $\widetilde{m}_j$ as on the true final memory.

Moreover, at most $(S(2^w - 1) + 1)^r$ memories over $S$ cells of $w$ bits lie within Hamming distance $r$ (counted in cells) of a fixed memory.

## Proof sketch

A cell not probed after epoch $j$ keeps its post-epoch-$j$ value, and a cell probed after epoch $j$ carries its final value in the overlay, which gives (1) and (2). Disjointness holds because a cell lies in $\mathrm{Last}_j$ only for the last epoch that probes it. Part (4) follows from (1) and the fact that a probe tree's answer depends only on the probed cells. The Hamming-ball count chooses, for each of $r$ positions, either nothing or one of the $S(2^w - 1)$ changes of one cell.

## Depends on

- [Chronogram epochs and last-probed cells](chronogram-epochs.md)

## Proof depends on

- [Counting bound for cell-probe trees](counting-bound-for-cell-probe-trees.md)

## Sources

- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
