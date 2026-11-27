# Paired t interval for normal differences

Let $n \ge 2$ and $0 < \alpha < 1$, and let $(X_i, Y_i)$, $i = 1, \dots, n$, be independent pairs; the two members of a pair may be dependent. Suppose the differences $D_i = X_i - Y_i$ are $N(\delta, \sigma^2)$ with $\sigma^2 > 0$. With $\bar D$ and $S_D^2$ the sample mean and sample variance (divisor $n - 1$) of the differences, $T = \sqrt n(\bar D - \delta)/S_D$ has the Student $t$ law with $n - 1$ degrees of freedom; $S_D = 0$ has probability zero, and $T$ may be defined as $0$ there. Hence $\bar D \pm t_{n-1, 1-\alpha/2} S_D/\sqrt n$ is an exact $1 - \alpha$ confidence interval for $\delta$. This is the one-sample $t$ interval applied to the differences; the pooled two-sample $t$ interval for independent samples with a common variance is a separate statement.

## Proof depends on

- [One-sample $t$ statistic](map-t-statistic-pi-gaussian-real.md): the one-sample $t$ statistic of i.i.d. normal data has the Student $t$ law with $n - 1$ degrees of freedom.

## Sources

- V. Dinh, *MATH 450: Mathematical statistics*, Lecture 24 "The paired t-test", University of Delaware, 2019, <https://vucdinh.github.io/F20/lecture24.pdf>
