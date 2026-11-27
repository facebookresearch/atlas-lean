# Finite Littlestone dimension implies private learnability

Every class $H$ of Littlestone dimension $1 \le d < \infty$ has, for every $\alpha > 0$, a globally stable realizable learner $G$ on $m = 2^{2^{d+2}+1} 4^{d+1} \lceil 2^{d+2}/\alpha \rceil$ samples: for every realizable distribution $D$ there is one fixed hypothesis $f_D$, depending on $D$ but not on the sample, with error at most $\alpha$ and $\Pr_{S \sim D^m,\,G}[G(S) = f_D] \ge \big((d+1) 2^{2^d+1}\big)^{-1}$. Merely outputting some accurate hypothesis with that probability would not suffice, since different samples could produce different accurate hypotheses and no output would recur. (A class of Littlestone dimension $0$ contains a single hypothesis and is trivially learnable.) Hence (Theorem 1), for all $\varepsilon, \delta \in (0,1)$ and $\alpha, \beta \in (0, 1/2)$ there is an $(\alpha,\beta)$-accurate $(\varepsilon,\delta)$-differentially private PAC learner for $H$ with sample complexity

$$
O\!\left(\frac{2^{\tilde O(2^d)} + \log(1/(\beta\delta))}{\alpha\, \varepsilon}\right).
$$

This sample complexity grows only logarithmically in $1/\delta$. Together with the $\Omega(\log^* d)$ lower bound of Alon, Livni, Malliaris and Moran (Corollary 2), which applies to $(\tfrac1{16}, \tfrac1{16})$-accurate learners on $n$ samples that are $(0.1, \delta)$-differentially private with $\delta = O(1/(n^2\log n))$, the following are equivalent for a class $H$: it is online learnable; it has finite Littlestone dimension; for all $\varepsilon, \delta \in (0,1)$ and $\alpha, \beta \in (0, 1/2)$ it has an $(\alpha,\beta)$-accurate $(\varepsilon,\delta)$-differentially private PAC learner with sample complexity polylogarithmic in $1/\delta$; and for some $n$ it has an $n$-sample $(\tfrac1{16}, \tfrac1{16})$-accurate $(0.1, O(1/(n^2\log n)))$-differentially private PAC learner. (The last two are linked because a sample size polylogarithmic in $1/\delta$ makes $\delta \le c/(n^2\log n)$ for all small enough $\delta$.) It is not enough for $\delta$ merely to tend to zero with the sample size: running an $m$-sample nonprivate learner on a uniformly random $m$-subset of $n$ examples is $(0, m/n)$-differentially private, so under that weaker requirement every PAC-learnable class, including thresholds on $\mathbb{N}$ with infinite Littlestone dimension, would count as privately learnable.

## Proof sketch

Run the Standard Optimal Algorithm on samples augmented with fictitious mistakes: draw a random number of tournaments in which the SOA is fed a sample together with examples where a previous output erred, so that each round of feedback lowers the Littlestone dimension of the version space. At some random depth at most $d$, the SOA output becomes a fixed function of the distribution with probability at least $2^{-2^{O(d)}}$, which is global stability; the stable-histogram lemma converts it into a private learner.

## Depends on

- [Global stability and list replicability of learning rules](../global-stability-and-list-replicability/global-stability-and-list-replicability.md)
- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Globally stable learners yield private learners via stable histograms](global-stability-to-private-learning.md)
- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)

## Sources

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563, Theorems 1, 3 and 10.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949, Corollary 2.
