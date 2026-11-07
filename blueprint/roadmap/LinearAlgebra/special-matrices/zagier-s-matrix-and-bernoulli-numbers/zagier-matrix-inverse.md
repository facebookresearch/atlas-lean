# Zagier's matrix conjecture

Let $K$ be a natural number, let $B_n$ be the $n$-th
Bernoulli number with $B_1 = -\frac{1}{2}$, and let $\binom{m}{k} = 0$ for $k > m$. Let $A$,
$P$ and $Q$ be the $(K - 1) \times (K - 1)$ rational matrices, with rows and columns indexed
by $1 \le i, j \le K - 1$, whose entries are

$$A_{ij} = \binom{2K - 2j}{2i - 1} + \binom{2K - 2j}{2K - 2i},$$



$$P_{ij} = \frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2j-1}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$



$$Q_{ij} = -\frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2K-2j}{2K-2i-n+1} \binom{n+2i-2}{n} B_n.$$

Then $P = Q$, $AP = I$ and $PA = I$, where $I$ is the identity matrix; that is, the two
Bernoulli formulas agree and give the two-sided inverse of $A$.

The source assumes $K \ge 2$. The assumption is not needed: for $K \le 1$ the matrices are
empty.

## Sources

- Yawen Ma and Lee-Peng Teo, "Another Proof of Zagier's Matrix Conjecture," Journal of Integer Sequences 25 (2022), Article 22.6.4, Theorem [Zagier's conjecture], equations (eq12) and (eq13), lines 279–285, https://cs.uwaterloo.ca/journals/JIS/VOL25/Teo/teo4.tex
