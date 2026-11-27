# Hybrid argument

For a linear isometry $O$, the final states of a $T$-query algorithm run with oracle $O$ and with no
oracle satisfy

$$\|\psi_T^{O} - \psi_T\| \le \sum_{k < T} \|O\varphi_k - \varphi_k\|,$$

where $\varphi_k$ is the oracle-free state just before query $k+1$. Each query can add at most the
amount by which $O$ moves the current oracle-free state, and later isometries do not amplify it. This is
the accounting in the proof of Theorem 3.3 of Bennett, Bernstein, Brassard and Vazirani (the difference
of final states is a sum of per-query errors carried forward by unitaries) and the statement that errors
along a unitary evolution only add (Bernstein and Vazirani, Theorem 3.4.1).

## Background

- [Run of a query algorithm](query-run.md): the query model.

## Sources

- C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and weaknesses of quantum computing", SIAM Journal on Computing 26 (1997), 1510–1523; arXiv:quant-ph/9701001, Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1 (theorem number as in that version).
