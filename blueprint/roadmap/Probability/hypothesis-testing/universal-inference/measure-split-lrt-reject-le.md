# Type I error of the split likelihood ratio test

In the setting of the [general universal confidence set](measure-not-mem-universal-confidence-set.md),
let $\Theta_0$ be a null set containing the true parameter $\theta^*$, and let $\hat\theta_0$ map each
second half $y$ to a parameter whose likelihood dominates that of every element of $\Theta_0$:
$q_\theta(y) \le q_{\hat\theta_0(y)}(y)$ for $\theta \in \Theta_0$. The maximum likelihood estimator
over $\Theta_0$ is an example. The split likelihood ratio test rejects $H_0 : \theta^* \in \Theta_0$
when $U = q_{\hat\theta_1}(D_0) / q_{\hat\theta_0(D_0)}(D_0) > 1/\alpha$, that is, when
$\alpha^{-1} q_{\hat\theta_0(D_0)}(D_0) < q_{\hat\theta_1}(D_0)$. For every $0 < \alpha < \infty$, with $\rho$ the law of $D_1$,

$$(\rho \otimes q_{\theta^*}\nu)\bigl(\{(w, y) : \alpha^{-1} q_{\hat\theta_0(y)}(y) < q_{\hat\theta_1(w)}(y)\}\bigr) \le \alpha.$$

When $\int q_{\theta^*} \, d\nu = 1$, so that $q_{\theta^*}\nu$ is the law of $D_0$, this says that the test rejects with
probability at most $\alpha$: its type I error is at most $\alpha$.

The proof is step (i) of Wasserman, Ramdas and Balakrishnan: under the null, replacing
$\hat\theta_0$ by $\theta^*$ can only increase $U$, so a rejection implies that the universal set
misses $\theta^*$. The statement assumes only the domination property of $\hat\theta_0$, which is
weaker than $\hat\theta_0$ being the maximiser.

## Informally uses

- [Finite-sample validity of the universal confidence set](measure-not-mem-universal-confidence-set.md): a rejection forces $\theta^* \notin C$.

## Background

- [Score, Wald and likelihood-ratio tests](../score-wald-and-likelihood-ratio-tests/README.md): the classical likelihood ratio test, whose level rests on Wilks's asymptotic chi-squared limit and hence on regularity of the model; the split test trades some power for a level guarantee in every model and every sample size.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Theorem 3 and its proof, in the generality of Remark 2.
