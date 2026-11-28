# Paired t interval for normal differences

Let $n \ge 2$ and $0 < \alpha < 1$. Let $(X_i,Y_i)$, for $i=1,\ldots,n$, be mutually independent pairs whose differences $D_i=X_i-Y_i$ all have law $N(\delta,v)$ with variance $v>0$. The two observations within a pair need not be independent.

With $\bar D$ the sample mean and $S_D^2$ the sample variance with divisor $n-1$, the statistic $T=\sqrt n(\bar D-\delta)/S_D$ has Student's $t$ law with $n-1$ degrees of freedom. Set $T=0$ when $S_D=0$; that event has probability zero. If $c$ is the quantile at $1-\alpha/2$ of that law, then $[\bar D-cS_D/\sqrt n,\,\bar D+cS_D/\sqrt n]$ contains $\delta$ with probability exactly $1-\alpha$.

The differences are independent because each is a measurable function of its own pair. Applying the one-sample $t$ result to the differences yields the pivot and the coverage, without using a pooled two-sample variance.

## Sources

- V. Dinh, *MATH 450: Mathematical Statistics*, [Lecture 24: The Paired t-Test](https://vucdinh.github.io/F20/lecture24.pdf), University of Delaware, 2019, for the reduction to a one-sample procedure on the differences. The argument here uses only independence across pairs and normality of the differences.
