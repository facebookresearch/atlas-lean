# Universal inference

Universal inference (Wasserman, Ramdas and Balakrishnan, PNAS 2020) gives confidence sets and
tests with finite-sample validity in any model with a likelihood, including irregular models such
as mixtures, where the likelihood ratio statistic has no tractable limit. Split the sample into
two independent halves $D_1$ and $D_0$, compute any estimate $\hat\theta_1$ from $D_1$, and
evaluate the likelihood $\mathcal L_0$ on $D_0$. A likelihood ratio has mean at most one under
its denominator, $E_{\theta^*}[\mathcal L_0(\psi) / \mathcal L_0(\theta^*)] \le 1$, so
Markov's inequality shows two things. The set
$\{\theta : \mathcal L_0(\hat\theta_1) / \mathcal L_0(\theta) \le 1/\alpha\}$ covers the
true parameter with probability at least $1 - \alpha$. The split likelihood ratio test, which
rejects when $\mathcal L_0(\hat\theta_1) / \mathcal L_0(\hat\theta_0) > 1/\alpha$ with
$\hat\theta_0$ the maximum likelihood estimator under the null, has type I error at most
$\alpha$. Both statements hold for an i.i.d. second half and for a general dominated
model.

- [Markov's inequality for a likelihood ratio](with-density-inv-mul-lt-le.md)
- [Universal confidence set](universal-confidence-set.md)
- [Finite-sample validity of the universal confidence set](measure-not-mem-universal-confidence-set.md)
- [Universal confidence set for an i.i.d. sample](measure-not-mem-universal-confidence-set-2.md)
- [Type I error of the split likelihood ratio test](measure-split-lrt-reject-le.md)
- [Split likelihood ratio test for an i.i.d. sample](measure-split-lrt-reject-le-pi.md)
- [Universal confidence set with real densities](universal-confidence-set-2.md)
- [Coverage of the universal confidence set with real densities](measure-not-mem-universal-confidence-set-3.md)

## Related topics

- [Score, Wald and likelihood-ratio tests](../score-wald-and-likelihood-ratio-tests/README.md): the classical likelihood ratio test, calibrated by Wilks's asymptotic chi-squared limit in regular models; universal inference splits the sample to get a level guarantee in every model and every sample size.
- [Neyman–Pearson lemma](../neyman-pearson-dominated-two-simple.md): the likelihood ratio between two simple hypotheses, whose mean under the null is at most one, the property universal inference rests on.
- [Valid p-values and false discovery proportion](../valid-p-values-and-false-discovery-proportion/README.md): by the same Markov argument, $1/U$ (capped at $1$) is a valid p-value for the null, the form Wasserman, Ramdas and Balakrishnan use for their anytime-valid p-values (arXiv:1912.11436v4, Section 8).
