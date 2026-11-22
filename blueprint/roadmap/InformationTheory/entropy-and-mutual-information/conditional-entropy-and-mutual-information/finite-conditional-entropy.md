# Conditional entropy of a finite joint law

Let $p$ be a probability distribution on
$\alpha \times \beta$, where $\alpha$ and $\beta$ are finite, viewed as the joint law of a pair
$(X, Y)$, and let $p_X(a) = \sum_{b \in \beta} p(a, b)$ be its first marginal. The conditional
entropy of $Y$ given $X$, in bits, is

$$H(Y \mid X) = -\sum_{a \in \alpha} \sum_{b \in \beta} p(a, b) \log_2 \frac{p(a, b)}{p_X(a)},$$

where every term with $p(a, b) = 0$ is $0$.

It is the finite counterpart of the conditional Shannon entropy given a sub-$\sigma$-algebra.
