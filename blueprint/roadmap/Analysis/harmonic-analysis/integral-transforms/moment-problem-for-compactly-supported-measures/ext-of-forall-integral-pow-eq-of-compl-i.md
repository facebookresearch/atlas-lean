# Compactly supported measures are determined by their moments

Let $\mu$ and $\nu$ be finite measures on $\mathbb{R}$ that give no mass to the complement of an
interval $[a, b]$. If $\int x^k \, d\mu = \int x^k \, d\nu$ for every $k \in \mathbb{N}$, then
$\mu = \nu$.

Proof: both integrals of every polynomial agree; by the Weierstrass approximation theorem, a
bounded continuous function is uniformly approximated on $[a, b]$ by polynomials, so its
integrals agree too; and a finite Borel measure on $\mathbb{R}$ is determined by the integrals of
bounded continuous functions.

## Background

- [Stieltjes moment problem](../stieltjes-moment-problem/README.md): background; Carleman's
  criterion gives uniqueness for measures on $[0, \infty)$ with moments growing slowly enough, of
  which compact support is the simplest case.

## Sources

- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Theorem 30.1 (a law whose moment
  series $\sum_k \alpha_k r^k / k!$ has a positive radius of convergence, in particular a compactly
  supported law, is determined by its moments).
- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §2.2.3.
