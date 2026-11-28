# Expected mistakes of independent Bernoulli predictions

Let $A$ be a randomized online
learner, which in round $t$ outputs
$p_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t) \in [0, 1]$ from the earlier examples and the
current instance, and let $S = ((x_1, y_1), \dots, (x_T, y_T))$ be a sequence with labels
$y_t \in \{0, 1\}$, fixed in advance. If the predictions
$\hat y_1, \dots, \hat y_T$ are independent and each $\hat y_t$ equals $1$ with probability $p_t$
and $0$ otherwise, then the expected number of mistakes is

$$\mathbb{E}\Big[\sum_{t=1}^T \mathbf{1}[\hat y_t \ne y_t]\Big]
= \sum_{t=1}^T \lvert p_t - y_t \rvert.$$

Labels and predictions are Booleans, false standing for $0$ and true for $1$, and the predictions
have the product of the Bernoulli distributions of parameters $p_1, \dots, p_T$ as their law.
