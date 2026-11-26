# Dilution-aware test counts and error rates for linear and square array testing

**Model.** $N$ people are screened; each is infected independently with prevalence $p$. An infected individual's sample has viral load $V=2^{-C_t}$, with $C_t$ drawn from a fitted distribution; a PCR test on a sample with cycle threshold $C_t$ is falsely negative with a logistic probability in $C_t$. A pool of size $n$ containing $d$ positive subsamples with loads $V_1,\dots,V_d$ has load $\frac1n\sum_{i=1}^dV_i$, i.e. cycle threshold $-\log_2\bigl(\frac1n\sum_i2^{-C_{t,i}}\bigr)$ (dilution). Let $\gamma(n,d)$ be the probability that such a pool tests negative (averaged over loads), with $\gamma(n,0)=1-q$ for a test false positive rate $q$; let $\eta(n,d)$ be the probability that a given positive sample in a pool with $d$ positives tests positive in the pool but negative on its individual follow-up. Each person's sample is split into identical-load subsamples for the pooled and follow-up tests.

**Linear array (two-stage) testing.** Pools of size $n$ are tested and every member of a positive pool is retested. Per person,

$$
M^L(n)=\frac1n+\sum_{d=0}^{n}\bigl(1-\gamma(n,d)\bigr)\binom nd p^d(1-p)^{n-d}
$$

is the expected number of tests,

$$
F^L(n)=\sum_{d=1}^{n}\bigl(\eta(n,d)+\gamma(n,d)\bigr)\binom{n-1}{d-1}p^d(1-p)^{n-d}
$$

is the expected number of false negatives, and

$$
\widetilde F^L(n)=q(1-p)\sum_{d=0}^{n-1}\bigl(1-\gamma(n,d)\bigr)\binom{n-1}{d}p^d(1-p)^{n-1-d}
$$

is the expected number of false positives. Analogous closed forms hold for $n\times n$ square arrays, where a sample is retested iff both its row and column pools are positive. The optimal pool size minimizes false negatives subject to $M(n)\le C$ (tests available per person), $\widetilde F(n)\le\widetilde C$ and $n\le\bar n$.

**Theorem (test correlation lowers false negatives).** Compare with the model in which all pooled and follow-up test results are conditionally independent given which samples contain virus. For both linear and square array protocols, the probability that a true positive is declared negative is no higher (in the source: lower) under the shared-viral-load model, and the probability that a true negative is declared positive is the same.

## Expansion

The test count is one pooled test per $n$ people plus $n$ follow-ups for each positive pool, averaged over the binomial number $d$ of positives in a pool. A positive person is missed either because its pool is negative ($\gamma$) or because the pool is positive but its own retest is negative ($\eta$), and conditioning on that person being infected leaves $d-1\sim\mathrm{Bin}(n-1,p)$ other positives. For the theorem, a positive sample is detected only if it is positive in every test it enters; each test's positivity probability is increasing in the shared load $V$, so since tests of one sample are conditionally independent given $V$, Chebyshev's association inequality for increasing functions of one random variable gives $\mathbb E[\prod_k g_k(V)]\ge\prod_k\mathbb E[g_k(V)]$, so joint detection is at least as likely as under independence (for square arrays the row and column pools share no other sample). False positives arise from contamination, which the model treats as independent of viral load, so they are unchanged; hence confirmatory repeat tests cut false positives with little cost in sensitivity.

## Sources

- Y. Lin, Y. Ren, J. Wan, M. Cashore et al., "Group testing enables asymptomatic screening for COVID-19 mitigation: feasibility and optimal pool size selection with dilution effects", arXiv:2008.06642 (2020), Section 3 (dilution model and pooled false negative rate), Section 4 (Theorem 1 in Section 4.3; Eqs. for $M^L$, $F^L$, $\widetilde F^L$, $M^S$ in Section 4.4) and the appendices on correlation and on linear and square array derivations, <https://doi.org/10.48550/arXiv.2008.06642>.
