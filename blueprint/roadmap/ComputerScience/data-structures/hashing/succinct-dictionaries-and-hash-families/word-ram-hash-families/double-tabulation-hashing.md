# Double tabulation hashing

Let $\Sigma = [2^b]$ and $c, d \ge 1$. A *double tabulation* function first applies a simple tabulation function $h_0 : \Sigma^c \to \Sigma^d$ (with $c$ tables of $d$-character entries) to obtain $d$ derived characters, and then applies a simple tabulation function $h_1 : \Sigma^d \to [2^M]$ to them: $h = h_1 \circ h_0$. Its seed is $(c + 1) \cdot d \cdot 2^b$ table entries.

## Depends on

- [Simple tabulation hashing](simple-tabulation-hashing.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
