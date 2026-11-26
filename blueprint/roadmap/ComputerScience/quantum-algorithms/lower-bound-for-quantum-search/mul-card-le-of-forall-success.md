# Lower bound for quantum search (BBBV)

In the setting of the [summed hybrid bound](sum-norm-query-run-sub-query-run-sq-le.md), let the
final measurement be given by linear maps $Q_y$ with $\sum_y \|Q_y v\|^2 \le \|v\|^2$ (outcome $y$ has
probability $\|Q_y v\|^2$), and let $\|\psi_0\| = 1$. If for every $y$ the algorithm run with oracle
$O_y$ outputs $y$ with probability at least $p$, then

$$p\, N \le 8T^2 + 2 .$$

For $p = 1/2$ this is $N \le 16T^2 + 4$, so $T \ge \sqrt{N - 4}/4$: unstructured search needs
$\Omega(\sqrt N)$ queries.

This is the query lower bound that Bennett, Bernstein, Brassard and Vazirani (Section 3.1) derive from
Theorem 3.3 and Corollary 3.4 and use to prove Theorem 3.5 (relative to a random oracle, NP is not
contained in BQTime$(o(2^{n/2}))$). The forms differ: their final step bounds the error probability of
an algorithm with $T \le 2^{n/2}/20$ relative to a random oracle through the total variation estimate of
Theorem 3.1, while the statement above concerns algorithms that succeed on every $y$ and ends with a
direct counting argument. The hypothesis $\|O_y v - v\| \le 2\|P_y v\|$ holds for the phase oracle and also for the
standard oracle $|z, b\rangle \mapsto |z, b \oplus [z = y]\rangle$ (with $P_y$ the projection onto the basis states whose query register holds $y$), so the bound covers both.

## Informally uses

- [Summed hybrid bound](sum-norm-query-run-sub-query-run-sq-le.md): $\sum_y \|\psi_T^y - \psi_T\|^2 \le 4T^2$.

## Background

- [Grover's algorithm](../grover-s-algorithm/README.md): attains $O(\sqrt N)$ queries, so the bound is tight up to a constant factor.

## Sources

- C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and weaknesses of quantum computing", SIAM Journal on Computing 26 (1997), 1510–1523; arXiv:quant-ph/9701001, Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1 (theorem number as in that version).
