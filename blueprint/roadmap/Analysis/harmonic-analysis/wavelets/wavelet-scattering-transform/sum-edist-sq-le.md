# Nonexpansiveness of a scattering cascade at every depth

Let $E, F$ be (pseudo-e)metric spaces, $A : E \to F$ and $U[\lambda] : E \to E$ for $\lambda \in \Lambda$, and suppose that one layer $f \mapsto (A f, (U[\lambda] f)_\lambda)$ is nonexpansive:

$$\|A f - A h\|^2 + \sum_{\lambda} \|U[\lambda] f - U[\lambda] h\|^2 \le \|f - h\|^2 .$$

Then for every depth $m$,

$$\sum_{n < m} \sum_{|p| = n} \|A U[p] f - A U[p] h\|^2 + \sum_{|p| = m} \|U[p] f - U[p] h\|^2 \le \|f - h\|^2$$

(the inequality chain in the proof of Proposition 2.5 of S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286)). Here $\|x - y\|$ stands for the distance, and squares and sums are taken in $[0, \infty]$.
