# Double tabulation hashing

Let $\Sigma = [2^b]$ and $c, d \ge 1$. A *double tabulation* function first applies a simple tabulation function $h_0 : \Sigma^c \to \Sigma^d$ (with $c$ tables of $d$-character entries) to obtain $d$ derived characters, and then applies a simple tabulation function $h_1 : \Sigma^d \to [2^M]$ to them: $h = h_1 \circ h_0$. Its seed consists of the $c$ first-stage tables, $c \cdot 2^b$ entries of $d$ characters each ($c d\, 2^b$ characters), and the $d$ second-stage tables, $d \cdot 2^b$ entries of $M$ bits. Thorup allows the derived characters to come from a second alphabet $\Psi$; this page takes $\Psi = \Sigma$.

## Depends on

- [Simple tabulation hashing](simple-tabulation-hashing.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
