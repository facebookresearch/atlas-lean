# Mistakes of a deterministic online learner

In online binary classification over rounds
$t = 1, \dots, T$, the environment reveals an instance $x_t \in X$, the learner predicts a label
$\hat y_t \in \{0, 1\}$, and then the true label $y_t \in \{0, 1\}$ is revealed. A deterministic
online learner $A$ predicts $\hat y_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t)$ from the
earlier examples and the current instance. Its number of mistakes on the sequence
$S = ((x_1, y_1), \dots, (x_T, y_T))$ is $\sum_{t=1}^T \mathbf{1}[\hat y_t \ne y_t]$. A hypothesis
$h : X \to \{0, 1\}$ is the learner that predicts $h(x_t)$ and ignores the earlier examples.

Labels are Booleans, false standing for $0$ and true for $1$.
