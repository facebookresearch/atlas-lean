# Natural policy gradient

Softmax policies and the natural policy gradient iteration, which for softmax policies is multiplicative weights on the advantages in every state, with its improvement lower bound and its dimension-free global convergence rate (Agarwal, Kakade, Lee and Mahajan 2021, Section 5.3).

## Softmax policies

- [Log-partition function](lse.md)
- [The partition function is positive](sum-exp-pos.md)
- [Softmax policy](softmax.md)
- [Action probabilities of a softmax policy](softmax-prob.md)
- [Softmax policies charge every action](softmax-prob-pos.md)
- [Softmax probabilities are at most one](softmax-prob-le-one.md)
- [Logarithm of a softmax probability](log-softmax-prob.md)
- [The softmax policy of zero logits is uniform](softmax-zero-prob.md)
- [Convexity of the log-partition function](sum-softmax-prob-mul-sub-le-lse-sub.md)
- [Gibbs' inequality for softmax policies](sum-softmax-mul-log-sub-nonneg.md)

## Natural policy gradient

- [Natural policy gradient iterates](npg-logits.md)
- [One natural policy gradient step](npg-logits-succ.md)
- [Natural policy gradient policies](npg-policy.md)
- [The NPG normalizer is at least one](lse-npg-logits-succ-sub-nonneg.md)
- [The NPG normalizer is bounded by the next policy's advantage](lse-npg-logits-succ-sub-le.md)
- [Improvement lower bound for natural policy gradient](npg-improvement.md)
- [Natural policy gradient never decreases the value](stoch-value-npg-policy-mono.md)
- [Global convergence of natural policy gradient](optimal-value-sub-stoch-value-npg-policy.md)

## Related topics

- [Hedge algorithm](../../online-learning-and-boosting/hedge-algorithm/README.md)
