# Mallows representation

For a real number $\alpha$, the Mallows representation
$M(\alpha) = M_1(\alpha) M_2(\alpha) \cdots$ is the infinite word over $\{L, M, R\}$ that records
the path of $\alpha$ down the Mallows tree. Fractions are written as numerator–denominator pairs.
Start with the gap between $0/1$ and $1/1$. At step $i \ge 1$, if the current gap lies between
$a = n_1/m_1$ and $b = n_2/m_2$, let $(p, q)$ be the pair that Mallows' rule inserts into it:
$p = (n_1 + n_2)/(m_1 + m_2)$ and $q = (n_1 + 2n_2)/(m_1 + 2m_2)$ if $n_1$ is even, and
$p = (2n_1 + n_2)/(2m_1 + m_2)$ and $q = (n_1 + n_2)/(m_1 + m_2)$ if $n_1$ is odd. Then
$M_i(\alpha) = L$ and the next gap is $(a, p)$ if $\alpha < p$; $M_i(\alpha) = M$ and the next
gap is $(p, q)$ if $p \le \alpha < q$; and $M_i(\alpha) = R$ and the next gap is $(q, b)$
otherwise.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Definition 4.
