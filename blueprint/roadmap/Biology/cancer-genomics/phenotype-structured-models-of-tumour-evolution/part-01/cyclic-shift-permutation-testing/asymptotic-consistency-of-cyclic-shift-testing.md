# Asymptotic consistency of cyclic shift testing

**Setting.** Let $\mathbf X$ be a random $n \times m$ matrix whose rows are independent copies of a first-order stationary ergodic Markov chain with countable state space $\mathcal A$, transition probabilities $p(u \mid v)$, and one- and two-dimensional marginals $p_1$ and $p_2$. Assume

$$\max_{u, v \in \mathcal A} p(u \mid v) < 1 \qquad \text{and} \qquad \frac{p_1(u)\, p_1(v)}{p_2(u, v)} < \infty \ \text{ for all } u, v \in \mathcal A,$$

with $0/0 := 0$; the second condition says $p_2(u, v) = 0$ forces $p_1(u) p_1(v) = 0$. Let $\mathcal S_m(\mathbf X)$ be the set of row-wise cyclic shifts of $\mathbf X$, let $P_{\mathbf X}(\cdot) = P_m(\cdot \mid \mathcal S_m(\mathbf X))$ be the *true conditional distribution* of the data given its shift orbit, and let $Q_{\mathbf X}$ be the uniform (cyclic conditional) distribution on $\mathcal S_m(\mathbf X)$.

**Theorem 1.** For each $m \ge 1$ let $T_m : \mathcal A^{n \times m} \to \mathbb R$ be invariant under constant shifts. Then

$$\max_{B \subseteq \mathbb R} \bigl| P_{\mathbf X}(T_m \in B) - Q_{\mathbf X}(T_m \in B) \bigr| \longrightarrow 0 \quad \text{in probability as } m \to \infty.$$

**Consequences.** $\sup_t |P_{\mathbf X}(T_m \ge t) - Q_{\mathbf X}(T_m \ge t)| \to 0$ in probability, and averaging over the data, $\sup_t |P_m(T_m \ge t) - Q_m(T_m \ge t)| \to 0$ with $Q_m = \mathbb E\, Q_{\mathbf X}$. Hence, for large $m$ and many resamples, the cyclic shift $p$-value has asymptotically correct type I error under the null of stationary ergodic rows.

**Extensions stated in the source.** The result extends to $k$th-order chains with fixed $k$, to rows that are independent chains with different transition laws (conditions holding row by row), and to continuous state spaces with transition density $f(u \mid v)$ when $f_1(X_1) f_1(X_m)/f_2(X_1, X_m) = O_P(1)$, which covers stationary Gaussian AR(1) rows.

## Expansion

*Distinct shifts.* If some $\sigma_k$ with $1 \le k < m$ fixes a row, the minimal such $k$ divides $m$ and the row is a repeated block (Lemma 2), so the row contains two disjoint equal blocks of length at least $m/3$ (Corollary 1). By the Markov property each such coincidence has probability at most $\rho^{l-1}$ with $\rho = \max p(u \mid v) < 1$ and $l \ge m/3$, so the orbit is "full" (all $m^n$ shifts distinct) with probability at least $1 - n\, m\, \rho^{m/3 - 1} \to 1$ (Lemma 3). On this event both $P_{\mathbf X}$ and $Q_{\mathbf X}$ reduce to distributions over the index vector $\mathbf k$ (Lemma 1).

*Comparing weights.* Under $P_{\mathbf X}$, shift $\mathbf k$ gets weight proportional to the Markov likelihood of $\sigma_{\mathbf k}(\mathbf X)$. Cyclically shifting a stationary Markov row changes its likelihood only through the transitions at the old and new break points, i.e. through ratios of the form $p_1(u) p_1(v)/p_2(u, v)$, which the second condition keeps finite. Because $T_m$ is invariant under constant shifts, only events invariant under a common shift matter; an ergodic averaging argument over the shift index (Lemma 4 and Corollary 2) shows these break-point factors average out, giving uniform agreement of $P_{\mathbf X}$ and $Q_{\mathbf X}$ on that invariant class (Theorem 2), from which Theorem 1 follows.

## Depends on

- [Cyclic shift permutation test for recurrent aberrations](cyclic-shift-permutation-test-for-recurrent-aberrations.md)

## Sources

- V. Walter, F. A. Wright, A. B. Nobel, "Consistent Testing for Recurrent Genomic Aberrations", arXiv:1403.1876 (2014), Theorem 1 (Section 2.5) and its proof in Section 4 (Lemmas 1–4, Corollaries 1–2, Theorem 2). <https://doi.org/10.48550/arXiv.1403.1876>
