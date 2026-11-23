# Brownian paths have unbounded variation

Let $B$ be a real Brownian motion and $t > 0$. Then almost surely the path $s \mapsto B_s$ does not have
bounded variation on $[0, t]$. The proof compares the quadratic sums $\sum_k (\Delta B_k)^2 \to t$ (in
probability, hence almost surely along a subsequence) with the vanishing quadratic sums of continuous
functions of bounded variation.

## Informally uses

- [Quadratic variation of Brownian motion in probability](tendsto-in-measure-sum-sq.md): the
  quadratic sums along the uniform partitions of $[0, t]$ tend to $t > 0$.
- [Quadratic sums of a continuous function of bounded variation vanish](tendsto-sum-sq-increments-of-bounded-var.md):
  on a path of bounded variation the same sums would tend to $0$.

## Background

- [Itô integral](../it-integral/README.md): because the paths have unbounded variation, $\int H\, dB$
  cannot be a pathwise Lebesgue–Stieltjes integral and is defined instead as an $L^2$ limit.
- [Signature of a path](../../../Analysis/rough-paths-and-path-signatures/signature-of-a-path/README.md): for the same reason the iterated
  integrals of a Brownian path are not defined pathwise; rough path theory adds the second level
  (the Lévy area) to the path as data.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapters 2 and 4.
