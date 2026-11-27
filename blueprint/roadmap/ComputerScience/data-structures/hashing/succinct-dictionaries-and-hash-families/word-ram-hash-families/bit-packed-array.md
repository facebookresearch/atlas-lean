# Bit-packed array on the Word RAM

A *bit-packed array* stores $N$ entries of $k \le w$ bits each in $\lceil N k / w \rceil + 2$ consecutive $w$-bit words: entry $i$ occupies bits $[ik, (i+1)k)$ of the concatenated words and may straddle two adjacent words. The word offset $\lfloor ik / w \rfloor$ and bit offset $ik \bmod w$ are computed as $\lfloor i / w \rfloor k + \lfloor (i \bmod w) k / w \rfloor$ and $(i \bmod w) k \bmod w$, so that every intermediate value stays below $2^w$. Reads and writes take $O(1)$ Word-RAM instructions.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- G. Navarro, "Compact Data Structures: A Practical Approach", Cambridge University Press, 2016, Section 3.1 (arrays of fixed-size elements).
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
