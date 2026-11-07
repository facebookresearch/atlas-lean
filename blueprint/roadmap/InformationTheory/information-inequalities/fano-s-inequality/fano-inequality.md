# Fano's inequality

Let $\alpha$ and $\beta$ be finite nonempty sets with $|\alpha| \ge 2$, let
$p : \alpha \times \beta \to \mathbb{R}$ satisfy $p(a, b) > 0$ for all $a, b$ and
$\sum_{a, b} p(a, b) = 1$, and let $g : \beta \to \alpha$ be an estimator. Put
$p_Y(b) = \sum_a p(a, b)$, let $P_e = \sum_b \sum_{a \ne g(b)} p(a, b)$ be the probability that
$g$ guesses wrong, and let $H(X \mid Y) = -\sum_{a, b} p(a, b) \log (p(a, b) / p_Y(b))$, where
$\log$ is the natural logarithm. Then

$$H(X \mid Y) \le -P_e \log P_e - (1 - P_e) \log (1 - P_e) + P_e \log (|\alpha| - 1).$$

## Sources

- R. M. Fano, Transmission of Information, MIT Press (1961). Proves `Wanted` entry `fano_inequality`. It follows from `fano_inequality_general`; the unused `[DecidableEq β]` keeps the source's shape.
