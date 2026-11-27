# Chronogram epochs and last-probed cells

Let a deterministic cell-probe scheme run consecutive operation segments $\mathrm{seg}_0, \mathrm{seg}_1, \dots, \mathrm{seg}_{L-1}$ (the *epochs*). For $j < L$, let $\mathrm{Later}_j$ be the set of cells probed during epochs $j+1, \dots, L-1$, and $\mathrm{Last}_j$ the set of cells probed during epoch $j$ and by no later epoch. The *overlay memory* $\widetilde{m}_j$ is the memory just before epoch $j$, overwritten on $\mathrm{Later}_j$ by the final contents of those cells. It is what a decoder can reconstruct from the pre-epoch memory together with the final contents of the cells probed after epoch $j$.

## Depends on

- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)

## Sources

- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
