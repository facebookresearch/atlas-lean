# Softmax and log-sum-exp

Softmax is evaluated stably by subtracting the largest input before exponentiating. Under a per-operation relative-error model that includes the exponential, the shifted evaluation has a first-order relative error growing linearly in the number of inputs and in the spread of the inputs.

- [Rounding error of the shifted softmax](rounding-error-of-the-shifted-softmax.md)

## Related topics

- [The online normalizer computes the softmax normalizer](../../../machine-learning/attention-and-low-rank-adaptation/online-normalizer-computes-the-softmax-normalizer.md): the one-pass computation of the same shifted normalizer in exact arithmetic.
