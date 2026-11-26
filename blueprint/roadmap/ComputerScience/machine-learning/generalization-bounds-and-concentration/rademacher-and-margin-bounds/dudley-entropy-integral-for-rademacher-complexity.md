# Dudley's entropy integral bound for empirical Rademacher complexity

For a sample $S \in Z^m$, $m > 0$, give functions $Z \to \mathbb{R}$ the empirical $L^2(P_m)$ distance $\|f - g\|_{S} = \sqrt{\frac{1}{m}\sum_i (f(S_i) - g(S_i))^2}$ and let $N_2(F, S, \varepsilon)$ be the covering number of $F$ at scale $\varepsilon$ in this distance. If $F$ lies within distance $R$ of some $f_0$, then for every $\alpha \in (0, R]$

$$
\hat{R}_S(F) \le 4\alpha + \frac{16}{\sqrt{m}}\int_{\alpha}^{R}\sqrt{\ln N_2(F, S, \varepsilon)}\, d\varepsilon,
$$

and the term $4\alpha$ can be dropped when the integrand is integrable on $[0, R]$. If $N_2(F, S, \varepsilon) \le (C/\varepsilon)^d$ for $\varepsilon \in (0, R]$ with $0 < R \le C$, then $\hat{R}_S(F) \le 16R\sqrt{d(1 + \ln(C/R))/m}$, with no $\ln m$ factor. For an $L$-Lipschitz parametrization $\theta \mapsto \Phi_\theta$ (in the empirical distance) of a ball of radius $r$ in a $d$-dimensional normed space, $N_2 \le (1 + 2Lr/\varepsilon)^d$; on a finite domain with values in $[a,b]$, with probability at least $1-\delta$ every parameter satisfies $\mathbb{E}_D\Phi_\theta \le \hat{\mathbb{E}}_S \Phi_\theta + 32Lr\sqrt{d(1 + \ln 3)/m} + (b-a)\sqrt{\ln(1/\delta)/(2m)}$. For a binary VC class with shattered sets of size at most $d$, $N_2(C, S, \varepsilon) \le (\sqrt{8}/\varepsilon)^{4d}$ for $0 < \varepsilon \le 1$.

## Proof sketch

Chain through nets at dyadic scales $R2^{-j}$ down to $\alpha$: the increments between consecutive nets are controlled by Massart's lemma, each contributing at most a constant times the scale times $\sqrt{\ln N_2}/\sqrt{m}$, and the sum is compared with the integral. The polynomial case integrates $\sqrt{d\ln(C/\varepsilon)}$; the Lipschitz case uses the volumetric covering bound of a ball, and the VC case lifts Dudley's Hamming packing bound.

## Depends on

- [Covering numbers and Dudley entropy integral](../rademacher-complexity/covering-numbers-and-dudley-entropy-integral.md)
- [Dudley's entropy bound](../../../../Probability/high-dimensional-probability/generic-chaining-and-gaussian-processes/integral-i-sup-le-dudley.md)
- [Empirical Rademacher complexity](../rademacher-complexity/rademacher-complexity.md)

## Proof depends on

- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Dudley's packing bound for classes of bounded VC dimension](../../pac-learning/sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)
- [Rademacher generalization bound for bounded function classes](rademacher-generalization-bound.md)
- [Dudley's chaining bound for Rademacher sums](../../../randomized-algorithms/random-strings-and-fingerprints/chaining-bound-for-rademacher-sums.md)

## Sources

- R. M. Dudley, "The Sizes of Compact Subsets of Hilbert Space and Continuity of Gaussian Processes", Journal of Functional Analysis, 1967.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
