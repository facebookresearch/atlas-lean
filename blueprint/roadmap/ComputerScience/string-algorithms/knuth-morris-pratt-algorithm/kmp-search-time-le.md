# KMP search makes linearly many comparisons

For any pattern $p$ and text $t$, lists over
a type with a Boolean equality test, KMP search for $p$ in $t$ makes at most $2|p| + 2|t|$ symbol
comparisons in total, those made while building the prefix table included, where $|p|$ and
$|t|$ are the lengths of $p$ and $t$.

The paper (Section 1) argues that after the table is set up at most $2n$ steps are performed on
a text of length $n$, because each step moves either the text pointer or the pattern to the right,
and (Section 2) that the table is computed in $O(m)$ steps by the same method. The bound
counts symbol comparisons of both phases together.

## Sources

- D. E. Knuth, J. H. Morris, Jr. and V. R. Pratt, "Fast pattern matching in strings", *SIAM J.
  Comput.* 6(2) (1977) 323–350, DOI 10.1137/0206024, Sections 1 and 2.
