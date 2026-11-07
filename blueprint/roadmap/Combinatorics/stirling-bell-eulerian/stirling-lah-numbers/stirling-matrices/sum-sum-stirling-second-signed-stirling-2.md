# Double-sum shift identity for Stirling numbers

Write $S(n, k)$ for the Stirling numbers
of the second kind and $s(n, k)$ for the signed Stirling numbers of the first kind. For all
natural numbers $i, j, n, m_1, m_2$ with $i \ge 1$, $n \ge i$ and $n \ge j$,

$$\sum_{k_1=1}^{n} \sum_{k_2=1}^{k_1} S(i+m_1, k_1)\, s(k_1, k_2)\, S(k_2+m_2, j) =
S(i+m_1+m_2, j).$$

The source leaves the shifts $m_1, m_2$ unquantified; here they are arbitrary natural numbers,
as in Corollary 3 of the source, and the source's hypothesis $j \ge 1$ is not needed.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Theorem 8 (`integers-2025-A27-thm-8`).
