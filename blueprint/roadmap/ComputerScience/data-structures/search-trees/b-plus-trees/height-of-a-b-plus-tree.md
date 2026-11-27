# Height of a B+-tree is logarithmic

Let a well-formed B+-tree of minimum degree $t \ge 2$ have height $h$ (counting the nodes on a root-to-leaf path, so a leaf has height $1$) and $N$ entries. A balanced subtree of height $h$ all of whose nodes are occupied holds at least $(t-1) t^{h-1}$ entries, and if $h \ge 2$ the whole tree holds at least $2(t-1) t^{h-2} \ge t^{h-1}$ entries. Consequently

$$
h \le \lfloor \log_t N \rfloor + 1 \quad (N \ge 1).
$$

## Proof sketch

An occupied interior node has at least $t$ children, so an occupied subtree of height $h$ has at least $t^{h-1}$ leaves with at least $t - 1$ entries each. A root of height at least $2$ has at least two occupied children of height $h - 1$.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
