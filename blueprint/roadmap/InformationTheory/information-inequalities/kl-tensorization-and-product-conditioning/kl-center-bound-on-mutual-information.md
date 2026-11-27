# KL-center bound on mutual information

Let $\mu$ be a prior on a finite set $V$, let $(P_v)_{v \in V}$ be distributions on a finite set $X$, and let $(X, V)$ have joint law $\mu(v) P_v(x)$. For every distribution $Q$ on $X$ whose support contains $\mathrm{supp}\,P_v$ for all $v \in \mathrm{supp}\,\mu$,

$$
I(X; V)\,\ln 2 = \sum_{v} \mu(v)\, D(P_v \,\|\, Q) - D\Big(\sum_v \mu(v) P_v \,\Big\|\, Q\Big) \le \sum_v \mu(v)\, D(P_v\,\|\,Q),
$$

with $I$ in bits and $D$ in nats. In particular, if $D(P_v\|Q) \le \beta$ for all $v \in \mathrm{supp}\,\mu$ then $I(X;V)\ln 2 \le \beta$, and if the supports of the $P_v$ agree then $I(X;V)\ln 2 \le \sum_{v,w}\mu(v)\mu(w) D(P_v\|P_w)$.

## Proof sketch

The identity is the reference-output decomposition of mutual information with the joint written as a mixture over $v$; dropping the nonnegative mixture divergence gives the bound. Taking $Q = P_w$ and averaging over $w \sim \mu$ gives the pairwise form.

## Depends on

- [Mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)
- [Reference-output decomposition of mutual information](../../not-yet-classified/part-01/reference-output-kl/kl-div-prod-reference-eq-measure-mutual.md)

## Proof depends on

- [Reference-output decomposition of mutual information](../../not-yet-classified/part-01/reference-output-kl/kl-div-prod-reference-eq-measure-mutual.md)
- [Gibbs' inequality](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)

## Sources

- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
