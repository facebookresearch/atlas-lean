# Energy identity of a scattering cascade

Let $E, F$ be seminormed groups, $A : E \to F$ and $U[\lambda] : E \to E$, and suppose that one layer preserves the norm, $\|A f\|^2 + \sum_\lambda \|U[\lambda] f\|^2 = \|f\|^2$. Then for every depth $m$,

$$\|f\|^2 = \sum_{n < m} \sum_{|p| = n} \|A U[p] f\|^2 + \sum_{|p| = m} \|U[p] f\|^2$$

(S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), proof of Theorem 2.6, equations (33)–(34)): the energy of $f$ splits into the scattering coefficients of order less than $m$ and the energy propagated to depth $m$. For the wavelet layer, $\|U[\lambda] f\| = \|f \star \psi_\lambda\|$ and Proposition 2.1 give the hypothesis.
