# Derivatives of the partition polynomial via Stirling numbers

Let $k \ge 1$, let
$m \colon \mathbb{N} \to \mathbb{N}$, and write $m_i = m(i)$. Assume $m_k \ne 0$ and $m_i = 0$
for every $i$ outside $\{1, \dots, k\}$, so that $m$ lists the part multiplicities of a
partition $\lambda = \langle 1^{m_1}, \dots, k^{m_k} \rangle$ with largest part $k$. Let
$f(y) = \sum_{i=1}^{k} m_i y^i$ for real $y$. Then for every natural number $d \le k$ and every
real $x \ne 0$,

$$f^{(d)}(x) = \sum_{i=1}^{k} i^d m_i x^{i-d} -
\sum_{j=0}^{d-1} S(d, j)\, x^{j-d} f^{(j)}(x),$$

where $S(d, j)$ are the Stirling numbers of the second kind and $f^{(j)}$ is the $j$th
derivative of $f$; for $d = 0$ the second sum is empty.

## Sources

- Madeline Locus Dawsey, Tyler Russell, and Dannie Urban, "Derivatives and Integrals of Polynomials Associated with Integer Partitions," Journal of Integer Sequences 25 (2022), Article 22.5.1, Theorem 1, lines 108–114, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.tex>.
