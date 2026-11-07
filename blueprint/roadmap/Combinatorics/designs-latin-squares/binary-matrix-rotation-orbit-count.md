# Counting binary matrices up to cyclic rotations

Let $m, n \ge 1$. For an $m \times n$
matrix $x$ with entries $x_{r,s} \in \{0, 1\}$, rows indexed by $0 \le r < m$ and columns by
$0 \le s < n$, put $N(x) = \sum_{r=0}^{m-1} \sum_{s=0}^{n-1} x_{r,s} \, 2^{rn+s}$, and for
$0 \le i < m$, $0 \le j < n$ let $x^{(i,j)}$ be the rotated matrix with entries
$x^{(i,j)}_{r,s} = x_{(r+i) \bmod m, \, (s+j) \bmod n}$. The number of such matrices $x$ with
$N(x) \le N(x^{(i,j)})$ for all $i$ and $j$ equals

$$\left\lfloor \frac{1}{mn} \sum_{c \mid m} \sum_{d \mid n} \varphi(c) \, \varphi(d) \,
2^{mn / \operatorname{lcm}(c,d)} \right\rfloor,$$

where $\varphi$ is Euler's totient function.

Since $N$ is injective, each orbit under the cyclic row and column rotations contains exactly one
such matrix, so this is the number of binary $m \times n$ matrices up to rotation; by Burnside's
lemma the division is exact (the Pólya enumeration formula).

## Sources

- S. N. Ethier, "Counting Toroidal Binary Arrays," Journal of Integer Sequences 16 (2013), Article 13.4.7, Theorem, lines 172–176, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Ethier/ethier2.tex>.
