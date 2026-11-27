# Omnipredictors

Let $D$ be a distribution over $X \times \{0,1\}$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a class of functions $c : X \to \mathbb{R}$. For a loss $\ell : \mathbb{R} \times \{0,1\} \to \mathbb{R}$ let $k_\ell(v)$ be an optimal action for a forecast $v$, a minimizer of $t \mapsto \mathbb{E}_{y \sim \mathrm{Ber}(v)}[\ell(t, y)]$ when one exists (ties broken arbitrarily), a univariate data-independent post-processing. The minimum need not be attained (the logistic loss at $v \in \{0,1\}$ has infimum $0$ and no minimizer), and the constructions restrict actions to an interval; in those cases $k_\ell(v)$ is an action whose expected loss is within a slack $\eta \ge 0$ of the infimum over the allowed actions, and that slack $\eta$ is added to the error of every guarantee below. For a family of losses $\mathcal{L}$, $p$ is an **$(\mathcal{L}, \mathcal{C}, \varepsilon)$-omnipredictor** if for every $\ell \in \mathcal{L}$

$$
\mathbb{E}_{(x,y) \sim D}\big[\ell(k_\ell(p(x)), y)\big] \le \inf_{c \in \mathcal{C}} \mathbb{E}_{(x,y) \sim D}\big[\ell(c(x), y)\big] + \varepsilon .
$$

The original definition of Gopalan, Kalai, Reingold, Sharan and Wieder only asks for some post-processing $k : [0,1] \to \mathbb{R}$ for each $\ell$, but their constructions use (an interval-restricted version of) $k_\ell$, and later work takes $k_\ell$ as part of the definition; the benchmark is an infimum because it need not be attained: for $\mathcal{C} = \{x \mapsto 1/j : j \ge 1\}$, the squared loss and $y = 0$ always, the losses $1/j^2$ have infimum $0$ and no minimizer in $\mathcal{C}$. The Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$ is an $(\mathcal{L}, \mathcal{C}, 0)$-omnipredictor for every $\mathcal{L}$ and $\mathcal{C}$ when each $k_\ell$ is an exact minimizer over all real actions, and an $(\mathcal{L}, \mathcal{C}, \eta)$-omnipredictor when each $k_\ell$ is $\eta$-approximate over all real actions. A single predictor thus serves as an agnostic learner for every loss in $\mathcal{L}$ simultaneously, the loss being chosen only after learning.

## Sources

- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389, Definition 4.1 and Lemma 4.2.
- P. Gopalan, L. Hu, M. P. Kim, O. Reingold, U. Wieder, "Loss Minimization through the Lens of Outcome Indistinguishability", ITCS (2023), arXiv:2210.08649, Definition 3.7.
