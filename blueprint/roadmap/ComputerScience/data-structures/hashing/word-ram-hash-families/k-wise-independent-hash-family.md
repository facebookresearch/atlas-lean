# k-wise independent hash family

Let $\Theta$ be a finite seed set with the uniform distribution and $h : \Theta \times X \to Y$ with $Y$ finite. The family $\{h_\theta\}$ is *$k$-wise independent* if for all pairwise distinct $x_1, \dots, x_k \in X$ and all $y_1, \dots, y_k \in Y$,

$$
\Pr_\theta\left[h_\theta(x_1) = y_1, \dots, h_\theta(x_k) = y_k\right] = |Y|^{-k}.
$$

It is *$\varepsilon$-universal* if $\Pr_\theta[h_\theta(x) = h_\theta(x')] \le \varepsilon$ for all $x \ne x'$; a $2$-wise independent family is $1/|Y|$-universal. A $k$-wise independent family is also $j$-wise independent for every $j \le k$.

## Depends on

- [Universal hash family](../universal-hashing/is-universal.md)
- [Four-wise independent random variables](../../../randomized-algorithms/frequency-moments-of-data-streams/four-wise-independent.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
