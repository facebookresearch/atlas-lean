# Entropy of a transformation relative to a partition

For a map $T : X \to X$ of a probability space $(X, \mu)$ and a family $\xi = (C_i)_{i \in I}$ of subsets of $X$
indexed by a finite set $I$ (typically a finite measurable partition),

$$h_\mu(T, \xi) = \limsup_{n \to \infty} \frac{1}{n}\, H_\mu\bigl(\xi \vee T^{-1}\xi \vee \dots \vee
T^{-(n-1)}\xi\bigr),$$

where the [dynamical refinement](iterate-join.md) has one atom for each word $(i_0, \dots, i_{n-1})$, the
points whose first $n$ symbols are $i_0, \dots, i_{n-1}$, and $H_\mu$ is the
[entropy of a finite partition](partition-entropy.md). The value is taken in $[0, \infty]$.

When $T$ is measurable and preserves $\mu$ and $\xi$ is a measurable partition, the sequence $H_\mu(\xi \vee \dots \vee T^{-(n-1)}\xi)$
is subadditive, so the limit exists and the $\limsup$ is that limit. Sinai writes the refinement with
$T^{-1}, \dots, T^{-n}$; by invariance this gives the same value.

## Sources

- Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009), §Definition (the limit exists
  by a subadditivity argument).
- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Definition 4.3.
