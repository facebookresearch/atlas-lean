# Folded-spectrum identifiability for piecewise families with growing pieces

When the ancestral state of each site is unknown, only the folded spectrum is observed: for a sample of size $n$, $\chi_{n,i} = (\xi_{n,i} + \xi_{n,n-i})/(1 + \delta_{i,n-i})$ for $1 \le i \le \lfloor n/2 \rfloor$. Let $F$ be a family of positive continuous population size functions on $\mathbb R_{\ge 0}$, and let $M_K(F)$ be the piecewise models over $F$ with at most $K$ pieces: population size functions $\eta$ with change points $0 = t_0 < t_1 < \cdots < t_p < t_{p+1} = \infty$, $p \le K - 1$, and $\eta(t) = f_i(t - t_{i-1})$ on $[t_{i-1}, t_i)$ with $f_i \in F$ (Bhaskar and Song 2014, Definitions 1 and 2). For families in which every member $f$ has $R_f(\infty) = \infty$ and a time-rescaled version of exponential order less than $1$, Bhaskar and Song's folded-spectrum theorem is stated in [identifiability of piecewise-exponential demographies from the frequency spectrum](../../site-frequency-spectrum-under-variable-populatio/sign-change-complexity-and-demographic-identifiability/identifiability-of-piecewise-exponential-demographies-from-the-sfs.md) (Theorem 12 there) and is not restated here. This page concerns families that contain members outside that class, such as growing exponential pieces, for which $R_f(\infty) < \infty$ and the time-rescaled version $\tilde f$ is defined only on $R_f(\mathbb R_{\ge 0})$ (their Definition 4). The sign change complexity $S(F)$ is the supremum, over $f_1, f_2 \in F$ and $a \ge 0$, of the number of sign changes of $\tau \mapsto \tilde f_1(\tau) - \tilde f_2(\tau - a)$ on its domain (their (2), Definitions 3 and 4, (5)). Two models are equivalent if they are related by the rescaling $\zeta(t) = \kappa\eta(t/\kappa)$, $\kappa > 0$, of Lemma 10. Bhaskar and Song (2014, Theorem 12) prove that if $S(F) < \infty$ and $n \ge 2(2K - 1)(1 + S(F))$, then each expected folded spectrum is consistent with a unique equivalence class of models in $M_K(F)$; the proof rests on a symmetry of the matrix relating branch lengths to first-coalescence means (their Lemma 13). The target is this statement for such families, among the models of $M_K(F)$ whose expected spectrum is finite (first-coalescence means $c_2, \dots, c_n$ finite), with the folded bound kept separate from the unfolded one.

## Depends on

- [Folded site frequency spectrum](../../expected-site-frequency-spectrum/folded-count.md)

## Proof depends on

- [Expected epoch lengths and first-coalescence means](epoch-lengths-first-coalescence-means.md)

## Expansion

1. The [folded spectrum](../../expected-site-frequency-spectrum/folded-count.md) and its expectation.
2. The linear map from expected epoch lengths to the expected folded spectrum, and its rank.
3. Theorem 12 for $K$-piece families of finite sign-change complexity that contain members outside the class covered by the linked folded-spectrum theorem (for example members with $R_f(\infty) < \infty$), via the symmetry of Lemma 13.
4. Whether the folded bound is tight, as a separate question.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, Definitions 1–4, equation (5), Lemma 10, Theorem 12 and Lemma 13. <https://arxiv.org/abs/1309.5056>
