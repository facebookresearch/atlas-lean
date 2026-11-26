# Zero patterns and the GM-MDS condition

A *zero pattern* for a $k \times n$ matrix is a tuple $(Z_1, \dots, Z_k)$ of subsets of $[n]$; a matrix $M$ *attains* it if $M_{i,j} = 0$ for every $j \in Z_i$. The pattern satisfies the *GM-MDS condition* if

$$
\Big|\bigcap_{i \in I} Z_i\Big| + |I| \le k \qquad \text{for every nonempty } I \subseteq [k].
$$

This condition is necessary for some generator matrix of an MDS code of dimension $k$ to attain the pattern, and it is sufficient for a generic matrix.

## Depends on

- [Linear code](../linear-codes/linear-code.md)

## Sources

- Son Hoang Dau, Wentu Song, Zheng Dong, Chau Yuen, "Balanced sparsest generator matrices for MDS codes", ISIT (2013).
- Shachar Lovett, "MDS matrices over small fields: a proof of the GM-MDS conjecture", FOCS (2018); arXiv:1803.02523.
