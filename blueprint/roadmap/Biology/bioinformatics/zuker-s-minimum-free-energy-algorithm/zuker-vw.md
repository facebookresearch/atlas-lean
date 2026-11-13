# Zuker's recursion

**Zuker's recursion** on the interval `[i, i + len)`, with `j = i + len - 1`, returning
`(V, WM)`:
* `V = ⊤` unless `(i, j)` can close a loop (`i + m < j`, `CanPair pair s i j`); otherwise `V` is
  the least of the hairpin energy `hairpin i j`, the interior-loop energies
  `interior i j k l + V(k, l)` over `i < k < l < j`, and the multiloop energies
  `a + WM(i + 1, u) + WM(u + 1, j - 1)` over `i < u < j - 1`;
* `WM` (a multiloop fragment with at least one branch, charging `b` per branch and `c` per
  unpaired base) is the least of `V + b`, `WM(i + 1, j) + c` (base `i` unpaired),
  `WM(i, j - 1) + c` (base `j` unpaired) and `WM(i, u) + WM(u + 1, j)` over `i ≤ u < j`.
Intervals are written by start and length.
