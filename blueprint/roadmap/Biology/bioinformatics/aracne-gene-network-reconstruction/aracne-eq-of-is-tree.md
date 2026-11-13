# ARACNE recovers tree networks exactly

**ARACNE recovers tree networks exactly** (Margolin et al. 2006, Theorem 1): if the true
network `T` is a tree whose edges all carry mutual information above `I₀`, and the strict
data-processing inequality holds on every separated triple, then ARACNE returns `T`. Strictness
is the explicit form of the paper's exclusion of exact cancellations; with equality ARACNE can
keep an indirect edge (see the tests).
