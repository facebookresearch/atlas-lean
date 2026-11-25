# Summed hybrid bound

Let $O_y$, for $y$ in a finite set of $N$ items, be linear isometries and $P_y$ maps with
$\|O_y v - v\| \le 2\|P_y v\|$ and $\sum_y \|P_y v\|^2 \le \|v\|^2$ for all $v$ ($\|P_y v\|^2$ is the
query magnitude of $y$ in $v$, Definition 3.2 of Bennett, Bernstein, Brassard and Vazirani). Then the
final states of a $T$-query algorithm satisfy

$$\sum_y \|\psi_T^{y} - \psi_T\|^2 \le 4T^2 \|\psi_0\|^2,$$

where $\psi_T^y$ uses the oracle $O_y$ and $\psi_T$ uses none.

Bennett et al. (Corollary 3.4) state the same accounting as a count: for unit $\psi_0$, all but
$2T^2/\varepsilon^2$ items $y$ satisfy $\|\psi_T^y - \psi_T\| \le \varepsilon$. The summed form
implies a count of the same shape (with $4T^2/\varepsilon^2$) by Markov's inequality.

## Informally uses

- [Hybrid argument](norm-query-run-sub-query-run-le.md): bounds each $\|\psi_T^{y} - \psi_T\|$ by $2\sum_k \|P_y \varphi_k\|$.

## Sources

- C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and weaknesses of quantum computing", SIAM Journal on Computing 26 (1997), 1510–1523; arXiv:quant-ph/9701001, Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1 (theorem number as in that version).
