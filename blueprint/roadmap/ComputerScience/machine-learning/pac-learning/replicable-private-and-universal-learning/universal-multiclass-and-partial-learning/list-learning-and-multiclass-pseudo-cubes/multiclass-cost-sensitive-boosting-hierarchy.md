# Multiclass cost-sensitive boosting thresholds form a finite hierarchy

Let $Y$ be finite with $|Y| = k$ and let $w : Y \times Y \to [0,1]$ be a cost function with zero diagonal, where $w(y, \hat y)$ is the cost of predicting $\hat y$ when the true label is $y$. Call a learner $A$ a $(w,z)$-learner for a class $F \subseteq Y^X$ if there is a single sample-size function $m_0 : (0,1)^2 \to \mathbb{N}$ such that for every $f \in F$, every distribution $D$ over $X$ and every $\varepsilon, \delta \in (0,1)$, on $m_0(\varepsilon,\delta)$ i.i.d. examples from $D$ labelled by $f$ it returns a predictor $h$ with $\mathbb{E}_{x \sim D}[w(f(x), h(x))] \le z + \varepsilon$ with probability at least $1-\delta$ over the sample and the learner's internal coins. There are finitely many thresholds $0 = v_1(w) < v_2(w) < \cdots < v_\tau(w) = V_Y(w)$ with $\tau \le 2^k$ depending on $w$, namely the distinct values $V_J(w) = \min_{p \in \Delta(Y)} \max_{q \in \Delta(J)} \mathbb{E}_{\hat y \sim p, y \sim q}[w(y, \hat y)]$ for nonempty label subsets $J \subseteq Y$ (the guesser's prediction $\hat y$ ranges over all labels $Y$, only the true label is restricted to $J$; $V_{\{y\}}(w) = 0$ gives $v_1 = 0$), such that, for $z \ge 0$ and $i$ the largest index with $v_i(w) \le z$ (so $z \in [v_i(w), v_{i+1}(w))$ when $i < \tau$, endpoint included), every $(w,z)$-learner can be boosted to a $(w, v_i(w))$-learner, but for some class $F$ some $(w,z)$-learner cannot be boosted to a $(w,z')$-learner for any $z' < v_i(w)$, while guarantees $z \ge v_\tau(w)$ are trivial (attained by a random guess). For the 0-1 cost these thresholds are the values $1 - 1/n$, $n = 1, \dots, k$ (so $\tau = k$). Moreover, for cost functions $w_1, \dots, w_r$ and $z \in [0,1]^r$, a learner meeting all $r$ guarantees exists if and only if, for every $\alpha \in \Delta_r$, a learner exists for the combined cost $\sum_i \alpha_i w_i$ with guarantee $\sum_i \alpha_i z_i$, and the equivalence is constructive.

## Proof sketch

The thresholds are values of zero-sum games between a random guesser restricted to label subsets of a given size ("dice" over subsets) and an adversary choosing the label distribution; between consecutive values, the weak learner beats every guesser over lists of the larger size, which is boostable to a list learner of the smaller size and then to the corresponding cost. The equivalence between multi-objective and cost-sensitive guarantees is a consequence of Blackwell's approachability theorem applied to the vector of costs.

## Depends on

- [List PAC learners and list learnability](list-pac-learner.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Cost-sensitive boosting dichotomy for binary classification](cost-sensitive-boosting-dichotomy.md)
- [Multiclass boosting with label-independent oracle complexity](multiclass-boosting-label-independent.md)

## Sources

- M. Bressan, N. Brukhim, N. Cesa-Bianchi, E. Esposito, Y. Mansour, S. Moran, M. Thiessen, "Of Dice and Games: A Theory of Generalized Boosting", COLT (2025), arXiv:2412.08012, Definitions 1 and 3, Equations (5)–(6), Fact 8, Theorems 6 and C.
- N. Brukhim, A. Daniely, Y. Mansour, S. Moran, "Multiclass Boosting: Simple and Intuitive Weak Learning Criteria", NeurIPS (2023), arXiv:2307.00642.
