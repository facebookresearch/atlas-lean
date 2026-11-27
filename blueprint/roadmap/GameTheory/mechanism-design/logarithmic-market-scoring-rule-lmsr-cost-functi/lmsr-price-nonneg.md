# Lmsr Price nonneg

For a finite nonempty set of outcomes, every real `b`, every share vector `q` and every outcome `i`, the LMSR price `exp(q i / b) / ∑ⱼ exp(q j / b)` (the softmax of `q / b` at `i`) is nonnegative.

At zero liquidity, $b = 0$, every quotient $q_j/b$ is $0$ and each price is $1/n$ for $n$ outcomes (see the [LMSR price](lmsr-price.md)).
