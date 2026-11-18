# A segment traversed out and back is tree-like

Let $x$ be a vector in a real normed space and $T \ge 0$. The path
$t \mapsto \min(t, T - t)\, x$ on $[0, T]$ runs linearly from $0$ to $\tfrac{T}{2} x$ and back to
$0$. It is [tree-like](is-tree-like.md), with height function $h(t) = \min(t, T - t)\, \|x\|$:
the increment between two times is at most the difference of their heights.

This is the simplest nonconstant path with trivial signature: it is the concatenation of a
segment with its own [time reversal](../signature-of-a-path/tensor-mul-signature-reverse.md).
