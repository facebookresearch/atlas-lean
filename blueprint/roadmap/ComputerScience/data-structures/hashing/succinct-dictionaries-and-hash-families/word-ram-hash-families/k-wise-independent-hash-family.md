# k-wise independent hash family

Let $\Theta$ be a finite nonempty seed set with the uniform distribution and $h : \Theta \times X \to Y$ with $Y$ finite and nonempty. The family $\{h_\theta\}$ is *$k$-wise independent* if for every $T \subseteq X$ with $|T| \le k$ and every $g : T \to Y$,

$$
\Pr_\theta\left[h_\theta(x) = g(x) \text{ for all } x \in T\right] = |Y|^{-|T|},
$$

that is, the restriction $h_\theta|_T$ is uniformly distributed on $Y^T$; equivalently, the values at any at most $k$ distinct points are independent and uniform on $Y$.

It is *$\varepsilon$-universal* (an $\varepsilon$-bounded universal family) if $\Pr_\theta[h_\theta(x) = h_\theta(x')] \le \varepsilon$ for all $x \ne x'$; a $2$-wise independent family is $1/|Y|$-universal. A $k$-wise independent family is also $j$-wise independent for every $j \le k$. Consequently, for any functions $g_x : Y \to \mathbb{R}$, $x \in T$, with $T \subseteq X$ and $|T| \le k$, the average over seeds of $\prod_{x \in T} g_x(h_\theta(x))$ equals $\prod_{x \in T} \mathbb{E}_{y \in Y}\, g_x(y)$.

## Depends on

- [Universal hash family](../../universal-hashing/is-universal.md)
- [Bounded universal hash functions](../../../../cryptography/hash-functions/bounded-universal-hash-functions.md)

## Informally uses

- [Four-wise independent random variables](../../../../randomized-algorithms/frequency-moments-of-data-streams/four-wise-independent.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981, Section 1 (strongly universal$_k$ classes).
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012, Definition 3.31.
