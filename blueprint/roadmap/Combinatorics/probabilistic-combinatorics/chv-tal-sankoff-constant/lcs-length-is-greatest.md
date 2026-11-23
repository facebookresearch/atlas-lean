# The LCS length is the maximum common-subsequence length

For binary strings $x$ and $y$ of
length $n$, let $\mathrm{LCS}(x, y)$ be the length returned by the dynamic-programming algorithm
for the longest common subsequence on $x$ and $y$. Then some common subsequence of $x$ and $y$
has length $\mathrm{LCS}(x, y)$, and every common subsequence of $x$ and $y$ has length at most
$\mathrm{LCS}(x, y)$.
