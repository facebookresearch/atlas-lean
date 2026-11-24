# Gromov's inequality

Let $M$ be a compact complex manifold of dimension $n$, $\Omega$ a smooth volume form on $M$, and
$\bar H_1, \dots, \bar H_l$ holomorphic line bundles on $M$ with smooth hermitian metrics. For integers
$m_1, \dots, m_l \ge 0$ give $m_1 H_1 + \dots + m_l H_l = H_1^{\otimes m_1} \otimes \dots \otimes
H_l^{\otimes m_l}$ the tensor product metric, with pointwise norm $|\cdot|$. There is a constant $C$,
depending only on $M$, $\Omega$ and $\bar H_1, \dots, \bar H_l$, such that for every real number
$p > 0$, all integers $m_1, \dots, m_l \ge 0$ and every $s \in H^0(M, m_1 H_1 + \dots + m_l H_l)$,

$$\max_{x \in M} |s|^p(x) \le C \lceil p \rceil^{2n} (m_1 + \dots + m_l + 1)^{2n} \int_M |s|^p \,
\Omega.$$

For $p = 2$ and one line bundle $\bar H$ this compares the sup norm and the $L^2$ norm on $H^0(M,
mH)$: $\lVert s \rVert_{\sup} \le C' (m + 1)^n \lVert s \rVert_{L^2}$ with $C' = 2^n C^{1/2}$, while
$\lVert s \rVert_{L^2} \le (\int_M \Omega)^{1/2} \lVert s \rVert_{\sup}$ trivially. Moriwaki deduces
the inequality from a local version on polydiscs (his Lemma 1.1.1), proved by the sub-mean-value
inequality for $|f|^p$ over polycircles, $f$ holomorphic and $p > 0$, and an elementary integral
estimate (his Claim 1.1.1.1), by covering $M$ with finitely many coordinate polydiscs on which the
metrics are close to constant. In one variable, the sub-mean-value inequality for $\log^+$ applied
to $f / \delta$, $\delta > 0$, gives $\log \max(|f(c)|, \delta) \le \frac{1}{2\pi} \int_0^{2\pi}
\log \max(|f(c + r e^{i\theta})|, \delta) \, d\theta$; Jensen's inequality for the convex function
$\exp(p \, \cdot)$ turns it into the same inequality for $\max(|f|, \delta)^p$, and letting $\delta
\to 0$, as $\max(t, \delta)^p$ differs from $t^p$ by at most $\delta^p$, gives $|f(c)|^p \le
\frac{1}{2\pi} \int_0^{2\pi} |f(c + r e^{i\theta})|^p \, d\theta$ for every $p > 0$. Applying it in
each variable in turn gives the polycircle form.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Sub-mean-value inequality for the positive logarithm of a holomorphic function](../../Analysis/complex-analysis/several-complex-variables/hartogs-theorem-on-separate-analyticity/hartogs-pos-log-norm-le-circle-average.md),
  applied to $f / \delta$, for the sub-mean-value inequality of $|f|^p$ on circles, through Jensen's
  inequality and $\delta \to 0$

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: §1.1, Lemma 1.1.1
  (local Gromov inequality) with its proof, pp. 6–7, and Corollary 1.1.2 (Gromov's inequality) with its
  proof, p. 8.
- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995), 187–221,
  author's scan of the printed edition <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>:
  (1.5), p. 190 (the comparison of $L^2$ and sup norms used in the proof of the arithmetic
  Hilbert–Samuel theorem).
