# Norm preservation is equivalent to the decay of the propagated energy

If one layer preserves the norm, $\|A f\|^2 + \sum_\lambda \|U[\lambda] f\|^2 = \|f\|^2$, then

$$\sum_{p} \|A U[p] f\|^2 = \|f\|^2 \iff \lim_{m \to \infty} \sum_{|p| = m} \|U[p] f\|^2 = 0,$$

the sum on the left running over all finite paths (S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), first paragraph of the proof of Theorem 2.6, equations (31)–(32)). The analytic content of Theorem 2.6 is that for [admissible wavelets](is-admissible.md) the propagated energy does tend to $0$; see [energy conservation](tsum-lintegral-windowed-scattering-eq.md).
