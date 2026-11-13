# Building a range tree from a list

For a range tree $s$, write $s_{\min}$ and $s_{\max}$
for its cached lower and upper bounds. The range tree built from a list $L$ of integers of length
$n$ is defined by recursion on $n$: the empty list gives the empty tree, a one-element list $[x]$
gives the leaf $x$, and for $n \ge 2$ it is the node whose left child $\ell$ is the tree built from
the first $\lfloor n/2 \rfloor$ entries of $L$, whose right child $r$ is the tree built from the
remaining entries, and whose cached interval is
$[\min(\ell_{\min}, r_{\min}), \max(\ell_{\max}, r_{\max})]$.

The entries of $L$ are kept in their given order; $L$ is not sorted first.
