# Entropy of a finite partition

For a finite family $\xi = (C_i)_{i \in I}$ of sets in a probability space $(X, \mu)$, its entropy is

$$H_\mu(\xi) = -\sum_{i \in I} \mu(C_i) \log \mu(C_i),$$

with the convention $0 \log 0 = 0$. For a partition of a probability space this is the Shannon entropy of
the probability vector $(\mu(C_i))_i$, the average information gained by learning which atom contains a
random point. The logarithm is natural, as in Sinai's article; Sarig uses $\log_2$, which divides every
entropy by $\log 2$.

## Sources

- Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009), §Definition.
- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Definition 4.1.
