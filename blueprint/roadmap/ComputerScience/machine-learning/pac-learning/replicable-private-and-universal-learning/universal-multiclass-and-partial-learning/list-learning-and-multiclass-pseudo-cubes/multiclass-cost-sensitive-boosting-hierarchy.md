# Multiclass cost-sensitive boosting thresholds form a finite hierarchy

Let $Y$ be finite with $|Y| = k$ and let $w : Y \times Y \to [0,1]$ be a cost function with zero diagonal, where $w(y, \hat y)$ is the cost of predicting $\hat y$ when the true label is $y$. Call a learner a $(w,z)$-learner for a class $F \subseteq Y^X$ if on every $F$-realizable distribution $D$ it outputs, from enough samples, hypotheses $h$ with $\mathbb{E}_{(x,y) \sim D}[w(y, h(x))] \le z + \varepsilon$ for every $\varepsilon > 0$. There are finitely many thresholds $0 = v_1(w) < v_2(w) < \cdots < v_\tau(w) = V_Y(w)$ with $\tau \le 2^k$ depending on $w$, namely the values $V_J(w) = \min_{p \in \Delta(Y)} \max_{q \in \Delta(J)} \mathbb{E}_{\hat y \sim p, y \sim q}[w(y, \hat y)]$ for label subsets $J \subseteq Y$, such that every $(w,z)$-learner with $z \in (v_i(w), v_{i+1}(w))$ can be boosted to a $(w, v_i(w))$-learner but in general not to a $(w,z')$-learner for any $z' < v_i(w)$, while guarantees $z \ge v_\tau(w)$ are trivial (attained by a random guess). For the 0-1 cost these thresholds are the values $1 - 1/n$, $n = 1, \dots, k$ (so $\tau = k$). Moreover, for cost functions $w_1, \dots, w_r$ and $z \in [0,1]^r$, a learner meeting all $r$ guarantees exists if and only if, for every $\alpha \in \Delta_r$, a learner exists for the combined cost $\sum_i \alpha_i w_i$ with guarantee $\sum_i \alpha_i z_i$, and the equivalence is constructive.

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
