# Expected number of mistakes of a randomized online learner

In online binary
classification over rounds $t = 1, \dots, T$, the environment reveals an instance $x_t \in X$, the
learner outputs a prediction, and then the label $y_t \in \{0, 1\}$ is revealed. A randomized
online learner $A$ outputs $p_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t) \in [0, 1]$,
computed from the earlier examples and the current instance, and then predicts $1$ with
probability $p_t$. Its expected number of mistakes on the sequence
$S = ((x_1, y_1), \dots, (x_T, y_T))$ is
$\sum_{t=1}^T \lvert p_t - y_t \rvert$, the absolute loss of the predictions $p_t$. Reading this
sum as an expectation is justified by
[expected mistakes of independent Bernoulli predictions](integral-mistakes-eq-expected-mistakes.md): when the
predictions $\hat y_t$ are independent and each equals $1$ with probability $p_t$, the expected
number of rounds with $\hat y_t \ne y_t$ is this sum.

Labels are Booleans, false standing for $0$ and true for $1$.
