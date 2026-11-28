# The left limit of the one-subject Kaplan–Meier estimator is one up to the observed time

Let $\Omega$ be a set and $T, C : \Omega \to \mathbb R$ a failure time and a censoring time, with observed time $X(\omega) = \min(T(\omega), C(\omega))$. The left limit of the one-subject Kaplan–Meier estimator is

$$\hat S(s-)(\omega) = \begin{cases} 0, & T(\omega) \le C(\omega) \text{ and } T(\omega) < s, \\ 1, & \text{otherwise}. \end{cases}$$

For every $s \in \mathbb R$ and $\omega \in \Omega$ with $s \le X(\omega)$,

$$\hat S(s-)(\omega) = 1.$$

See the [left limit](kaplan-meier-one-left.md).
