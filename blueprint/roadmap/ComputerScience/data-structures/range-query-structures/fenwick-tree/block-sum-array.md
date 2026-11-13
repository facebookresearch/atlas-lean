# Interval sum read from an array

For an array $a$ of elements of a commutative additive
monoid $\alpha$ and a natural number $j$, this is the sum of the $\operatorname{lowbit}(j)$
entries of $a$ ending at zero-indexed position $j - 1$, where $\operatorname{lowbit}(j)$ is the
largest power of two dividing $j$ (with $\operatorname{lowbit}(0) = 0$) and entries past the
end of $a$ count as $0$.

It has the same value as the list-based interval sum but reads each entry in constant time;
Fenwick-tree construction uses it, so building takes $O(n \log n)$ reads rather than quadratic
list indexing.
