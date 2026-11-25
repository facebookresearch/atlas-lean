# Grundy numbers of Maximum Nim

For a rule function $f : \mathbb{N} \to \mathbb{N}$, the
Grundy number $G_f(x)$ of a pile of $x$ stones in Maximum Nim is defined by recursion on $x$ as the
mex (least natural number not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$, the
Grundy numbers of the positions reachable from $x$ by removing $u$ stones.

Taking $\min(f(x), x)$ makes the definition total; under the source's hypotheses on $f$, which
include $f(0) = 0$, it does not change the legal moves.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Section 2.
