# Candidate sparsification of loop-based MFE folding

**Setting.** For an RNA sequence $S = S_1 \cdots S_n$ and a loop-based (nearest-neighbour) energy model, the [Zuker recursions](../../zuker-s-minimum-free-energy-algorithm/zuker-mfe.md) use $W(i,j)$ (MFE of $S_i \cdots S_j$), $V(i,j)$ (MFE with $i$ paired to $j$), and $WM(i,j)$ (MFE of a multiloop fragment), with multiloop parameters $a$ (closing), $b$ (per inner pair) and $c$ (per unpaired base). Introduce $W^p(i,j)$, the MFE of $S_i \cdots S_j$ among structures that decompose into two independent parts, and $WM^2(i,j)$, the MFE of multiloop fragments with at least two inner base pairs. An interval $[k,j]$ is a *W-candidate* if its optimal structure is closed by the pair $k \cdot j$ and cannot be split, $V(k,j) < W^p(k,j)$, and analogously a *WM-candidate* with respect to $WM$.

**Sparsified recursions.**

$$\widehat{W}^p(i,j) = \min\Bigl\{W(i, j-1),\; \min_{[k,j]\ \text{W-candidate},\, k > i} W(i, k-1) + V(k,j)\Bigr\},$$

$$\widehat{WM}^2(i,j) = \min\Bigl\{WM^2(i, j-1) + c,\; \min_{[k,j]\ \text{WM-candidate},\, k > i} WM(i, k-1) + V(k,j)\Bigr\}.$$

**Results.** Let $Z$ be the total number of candidates and $T$ the maximum number of accessible trace arrows to non-candidates (both at most $n^2$, typically much smaller).

1. The sparsified recursions for $W^p$ and $WM^2$ give the same values as the unsparsified ones (and replacing $WM^p$ accordingly leaves $W$, $V$, $WM$ unchanged).
2. $W(1,n)$ is computed in $O(n^2 + nZ)$ time and $\Theta(n + Z)$ space, versus $O(n^3)$ time and $O(n^2)$ space.
3. The minimization over inner base pairs in the recursion for $V$ (interior loops) cannot be restricted to candidates: in the Turner model the sequence GCCAAAAGGGC is a counterexample.
4. With trace arrows stored only for non-candidate entries still accessible during evaluation, and garbage-collected otherwise, the MFE structure (not just its energy) is obtained in $O(n^2 + nZ)$ time and $\Theta(n + Z + T)$ space.

## Depends on

- [Zuker's recursion](../../zuker-s-minimum-free-energy-algorithm/zuker-vw.md)
- [Zuker minimum free energy](../../zuker-s-minimum-free-energy-algorithm/zuker-mfe.md)

## Expansion

For item 1, take the largest split point $k$ attaining the minimum of $W(i,k-1) + W(k,j)$; if $[k,j]$ were not a candidate, it would itself split at some $e > k$, and regrouping $W(i,k-1) + W(k,e-1) \ge W(i,e-1)$ produces an optimal split with larger index, a contradiction. So only candidate right parts need to be scanned, and each candidate list is stored per right end $j$, using $O(n)$ rolling rows of the DP matrices. Interior loops break this argument because their energy depends on the inner pair's position, not only on $V$, which is why item 3 requires keeping a bounded window of $V$ rows and trace arrows.

## Sources

- S. Will and H. Jabbari, "Sparse RNA folding revisited: space-efficient minimum free energy structure prediction", *Algorithms for Molecular Biology* (2016), Results (sparsified recurrences and candidate criteria), Lemmas 1–6 and Definition 1. <https://doi.org/10.1186/s13015-016-0071-y> (PMC4842305)
