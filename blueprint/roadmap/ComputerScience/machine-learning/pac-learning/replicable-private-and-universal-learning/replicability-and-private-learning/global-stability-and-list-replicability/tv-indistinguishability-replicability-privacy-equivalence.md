# TV indistinguishability, replicability and approximate privacy are equivalent for PAC learning

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Then:

- every $n$-sample $\rho$-replicable rule is $n$-sample $\rho$-TV indistinguishable;
- on a countable domain, every $n$-sample $\rho$-TV indistinguishable rule has an equivalent rule (with the same output distribution on every sample) that is $n$-sample $\tfrac{2\rho}{1+\rho}$-replicable, obtained by coupling the two output distributions through shared randomness;
- for $\gamma \in (0, 1/2)$, if a class $H \subseteq \{0,1\}^X$ is learnable by an $n$-sample $(\tfrac12 - \gamma, \tfrac12 - \gamma)$-accurate (error at most $\tfrac12 - \gamma$ with probability at least $\tfrac12 + \gamma$) $(0.1, 1/(n^2 \log n))$-differentially private learner, then for all $\alpha, \beta, \rho \in (0,1)$ it is learnable by an $(\alpha, \beta)$-accurate $\rho$-TV indistinguishable rule;
- on a countable domain, if $H$ is learnable by an $(\alpha, \beta)$-accurate $\rho$-TV indistinguishable learner with $\rho \in (0,1)$, $\alpha \in (0, \tfrac12)$ and $\beta \in \big(0, \tfrac{1-\rho}{1+\rho}\big)$, then for all $\alpha', \beta', \varepsilon, \delta \in (0,1)$ it is learnable by an $(\alpha + \alpha', \beta')$-accurate $(\varepsilon,\delta)$-differentially private learner.

Consequently, for every domain $X$ and every class $H \subseteq \{0,1\}^X$ the following are equivalent: (i) $H$ is replicably learnable, that is, for all $\alpha, \beta, \rho \in (0,1)$ it has an $(\alpha,\beta)$-accurate $\rho$-replicable learner on finitely many samples; (ii) for some $n$ and some $\gamma \in (0, \tfrac12)$, $H$ has an $n$-sample $(\tfrac12 - \gamma, \tfrac12 - \gamma)$-accurate $(0.1, 1/(n^2\log n))$-differentially private learner, the regime of the third item (Alon, Livni, Malliaris and Moran state their lower bound for $(\tfrac1{16}, \tfrac1{16})$-accuracy in the same privacy regime $\varepsilon = 0.1$, $\delta = O(1/(n^2\log n))$); (iii) for all $\varepsilon, \delta \in (0,1)$ and $\alpha, \beta \in (0, \tfrac12)$, $H$ has an $(\alpha,\beta)$-accurate $(\varepsilon,\delta)$-differentially private learner whose sample complexity grows only polylogarithmically in $1/\delta$; (iv) $H$ has finite Littlestone dimension. Here (ii) implies (iv) by the private-learning lower bound of Alon, Livni, Malliaris and Moran, as used in the proof of the third item; (iv) implies (iii) by Bun, Livni and Moran, whose learner uses $O_d(\log(1/(\beta\delta))/(\alpha\varepsilon))$ samples; (iii) implies (ii) because when the sample size $n$ is polylogarithmic in $1/\delta$, so is $n^2\log n$, hence $\delta \le 1/(n^2\log n)$ for all small enough $\delta$; (iv) implies (i) because the proof of the third item builds a replicable learner from a globally stable one through replicable heavy hitters; and (i) implies (iii) by the replicability-to-privacy transformation of Bun et al. (Theorem 3.1), whose sample cost is polylogarithmic in $1/\delta$. The privacy parameter must be tied to the sample size in this way: it is not enough for $\delta$ merely to tend to zero, since running an $m$-sample nonprivate learner on a uniformly random $m$-subset of $n$ examples is $(0, m/n)$-differentially private, so every PAC-learnable class, thresholds on $\mathbb{N}$ included despite their infinite Littlestone dimension, would have private learners for every fixed $\delta > 0$ with $\delta \to 0$ as $n \to \infty$.

## Proof sketch

Replicability implies TV indistinguishability because for fixed samples the probability over shared randomness that two runs disagree upper bounds the total variation distance of the output distributions. The converse uses correlated sampling: given two distributions at total variation distance $t$, a shared random sequence of proposals with rejection sampling produces coupled outputs that agree with probability at least $(1-t)/(1+t)$. The privacy links go through global stability: a private learner forces finite Littlestone dimension, Littlestone classes have globally stable learners, and replicable heavy hitters turn global stability into replicability.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Total-variation indistinguishable learning rules](tv-indistinguishable-learning-rule.md)
- [Private PAC learners and their sample complexity](../private-learning-and-littlestone-classes/private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Replicable heavy hitters with domain-independent sample complexity](replicable-heavy-hitters.md)
- [Private learning requires log-star of the Littlestone dimension samples](../private-learning-and-littlestone-classes/private-learning-requires-log-star-littlestone.md)
- [Finite Littlestone dimension implies private learnability](../private-learning-and-littlestone-classes/littlestone-classes-are-privately-learnable.md)
- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)
- [Sample-efficient reductions between replicability and approximate differential privacy](replicability-privacy-reductions.md)

## Sources

- A. Kalavasis, A. Karbasi, S. Moran, G. Velegkas, "Statistical Indistinguishability of Learning Algorithms", ICML (2023), arXiv:2305.14311, Theorems 1–5, Corollary 1 and Remark 4.
- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921, Theorem 3.1.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949, Corollary 2.
- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563, Theorem 1.
