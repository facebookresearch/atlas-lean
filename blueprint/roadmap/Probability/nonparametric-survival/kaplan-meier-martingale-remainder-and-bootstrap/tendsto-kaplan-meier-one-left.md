# Left limit of the one-subject Kaplan–Meier estimator

Let $\Omega$ be a set and $T, C : \Omega \to \mathbb R$ a failure time and a censoring time, with observed time $X(\omega) = \min(T(\omega), C(\omega))$. The one-subject Kaplan–Meier estimator $\hat S(t)(\omega)$ is the grouped-data Kaplan–Meier estimate of the sample with the single observation time $X(\omega)$, death count $d(\omega) = \mathbf 1\{T(\omega) \le C(\omega)\}$ and censoring count $1 - d(\omega)$:

$$\hat S(t)(\omega) = \begin{cases} 1 - d(\omega), & X(\omega) \le t, \\ 1, & t < X(\omega). \end{cases}$$

Let

$$\hat S(t-)(\omega) = \begin{cases} 0, & T(\omega) \le C(\omega) \text{ and } T(\omega) < t, \\ 1, & \text{otherwise}. \end{cases}$$

Then for every $t \in \mathbb R$ and $\omega \in \Omega$, $\hat S(s)(\omega) \to \hat S(t-)(\omega)$ as $s \to t$ with $s < t$. See the [estimator](kaplan-meier-one.md) and its [left limit](kaplan-meier-one-left.md).
