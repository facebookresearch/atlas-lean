# Universe-reduced two-stage hashing

A *universe-reduced* hash first maps a key $u \in [U]$, $U \le 2^{w_0}$, to a reduced key $r(u) \in [2^R]$, $1 \le R \le w_0$, by multiply-shift (computed without double-width products), and then applies a hash family designed for the small universe $[2^R]$, for example a $k$-wise independent polynomial hash or a double tabulation function, possibly salted by appending a salt character. On a window $W$ of keys, fixed independently of the seeds, on which $r$ is injective, the composite inherits the independence properties of the second stage; injectivity fails with probability at most $|W| (|W|-1) / 2^R$. When every table entry fits in a word ($q \le w$ for the polynomial coefficients, $db \le w$ and $M \le w$ for double tabulation), storing the second-stage seed in bit-packed arrays, one per table, makes it occupy at most $B / w + 3t$ words, where $B$ is its size in bits and $t$ its number of tables: $B = kq$ for a polynomial hash over $\mathbb{F}_{2^q}$, and $B = 2^b d (c b + M)$ for double tabulation $\Sigma^c \to \Sigma^d \to [2^M]$ with $\Sigma = [2^b]$; the multiplier of the first stage takes one more word.

## Depends on

- [Multiply-shift is 2/2^M-universal](multiply-shift-is-universal.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](polynomial-hashing-is-k-wise-independent.md)
- [Double tabulation hashing](double-tabulation-hashing.md)
- [Bit-packed array on the Word RAM](bit-packed-array.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121, Section 1.1 (universe reduction by universal hashing before tabulation).
- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms 25(1), 1997, Lemma 2.6.
