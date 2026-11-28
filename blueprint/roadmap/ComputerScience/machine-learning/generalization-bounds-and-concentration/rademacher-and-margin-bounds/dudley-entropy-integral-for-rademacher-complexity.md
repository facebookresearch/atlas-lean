# Dudley's entropy integral bound for empirical Rademacher complexity

For a sample $S = (z_1, \ldots, z_m) \in Z^m$, $m > 0$, give functions $Z \to \mathbb{R}$ the empirical $L^2(P_m)$ distance $\|f - g\|_{S} = \sqrt{\frac{1}{m}\sum_i (f(z_i) - g(z_i))^2}$ and let $N_2(F, S, \varepsilon)$ be the covering number of $F$ at scale $\varepsilon$ in this distance. There is an absolute constant $C$ such that for every class $F$ of functions $Z \to \mathbb{R}$ and every sample $S$

$$
\hat{R}_S(F) \le \frac{C}{\sqrt{m}}\int_0^\infty \sqrt{\ln N_2(F, S, \varepsilon)}\, d\varepsilon.
$$

In discrete form, let $A = \{(f(z_1), \ldots, f(z_m)) : f \in F\} \subseteq \mathbb{R}^m$ be bounded, let $N(r, A)$ be its covering number at scale $r$ in the Euclidean norm and $c = \min_{\bar a}\max_{a \in A}\|a - \bar a\|$. Then for every integer $M > 0$

$$
\hat{R}_S(F) \le \frac{c\,2^{-M}}{\sqrt{m}} + \frac{6c}{m}\sum_{k=1}^{M} 2^{-k}\sqrt{\ln N(c\,2^{-k}, A)}.
$$

## Proof sketch

The integral form is Dudley's inequality applied, conditionally on $S$, to the mean-zero Rademacher process $X_f = m^{-1/2}\sum_i \sigma_i f(z_i)$ on $(F, \|\cdot\|_S)$, whose increments are sub-gaussian with an absolute constant by Hoeffding's inequality; then $\hat{R}_S(F) = m^{-1/2}\,\mathbb{E}_\sigma\sup_f X_f$. The discrete form chains through Euclidean covers of $A$ at the dyadic scales $c\,2^{-k}$, bounding each link by Massart's finite-class lemma.

Explicit constants. If $F$ lies within distance $R$ of some $f_0$, then $R' = c/\sqrt{m} \le R$ and $N(\sqrt{m}\,r, A) \le N_2(F, S, r)$; since $N_2$ is nonincreasing in $\varepsilon$, each term $R'\,2^{-k}\sqrt{\ln N_2(F, S, R'\,2^{-k})}$ is at most twice the integral of $\sqrt{\ln N_2}$ over $[R'\,2^{-k-1}, R'\,2^{-k}]$. Choosing the largest $M$ with $R'\,2^{-M-1} \ge \alpha$, so that $R'\,2^{-M} < 4\alpha$, and using $\hat{R}_S(F) \le R'$ (Cauchy-Schwarz) when $\alpha > R'/4$, gives $\hat{R}_S(F) \le 4\alpha + \frac{12}{\sqrt m}\int_\alpha^R \sqrt{\ln N_2(F, S, \varepsilon)}\,d\varepsilon$ for every $\alpha \in (0, R]$, and the term $4\alpha$ can be dropped when the integrand is integrable on $[0, R]$. If $N_2(F, S, \varepsilon) \le (C_0/\varepsilon)^d$ for $\varepsilon \in (0, R]$ with $0 < R \le C_0$, Cauchy-Schwarz gives $\int_0^R \sqrt{\ln(C_0/\varepsilon)}\,d\varepsilon \le R\sqrt{1 + \ln(C_0/R)}$, so $\hat{R}_S(F) \le 12R\sqrt{d(1 + \ln(C_0/R))/m}$, with no $\ln m$ factor. For an $L$-Lipschitz parametrization $\theta \mapsto \Phi_\theta$ (in the empirical distance) of a ball of radius $r$ in a $d$-dimensional normed space, the volumetric bound gives $N_2 \le (1 + 2Lr/\varepsilon)^d \le (3Lr/\varepsilon)^d$ for $\varepsilon \le Lr$, and the Rademacher generalization bound then gives, for values in $[a,b]$ and with probability at least $1-\delta$, $\mathbb{E}_D\Phi_\theta \le \hat{\mathbb{E}}_S \Phi_\theta + 24Lr\sqrt{d(1 + \ln 3)/m} + (b-a)\sqrt{\ln(1/\delta)/(2m)}$ for every parameter. For a binary VC class $\mathcal{C}$ with shattered sets of size at most $d$, lifting Dudley's Hamming packing bound gives $N_2(\mathcal{C}, S, \varepsilon) \le (\sqrt{8}/\varepsilon)^{4d}$ for $0 < \varepsilon \le 1$.

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
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018, Theorem 8.1.3 and the proof of Theorem 8.3.23.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Lemma 27.4.
