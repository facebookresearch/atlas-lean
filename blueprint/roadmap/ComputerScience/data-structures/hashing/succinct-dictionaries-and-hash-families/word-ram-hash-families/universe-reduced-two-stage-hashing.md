# Universe-reduced two-stage hashing

A *universe-reduced* hash first maps a key $u \in [U]$, $U \le 2^{w_0}$, to a reduced key $r(u) \in [2^R]$ by multiply-shift (computed without double-width products), and then applies a hash family designed for the small universe $[2^R]$, for example a $k$-wise independent polynomial hash or a double tabulation function, possibly salted by appending a salt character. On a window $W$ of keys on which $r$ is injective, the composite inherits the independence properties of the second stage; injectivity fails with probability at most $|W| (|W|-1) / 2^R$. Storing the second-stage tables in bit-packed arrays makes the seed size $O(k) + o(2^b)/w$ words independently of the machine word size.

## Depends on

- [Multiply-shift is 2/2^M-universal](multiply-shift-is-universal.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](polynomial-hashing-is-k-wise-independent.md)
- [Double tabulation hashing](double-tabulation-hashing.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms 25(1), 1997.
