# Kolmogorov's extension theorem for sequences

Probability measures $\mu_n$ on $\mathbb R^n$, one for each $n$, that are consistent, in the sense that
$\mu_n$ is the law of the first $n$ coordinates under $\mu_{n+1}$, come from a unique probability measure $P$ on the
space $\mathbb R^{\mathbb N}$ of real sequences: under $P$, the first $n$ coordinates have law $\mu_n$ for every $n$. This is
the classical case, with uniqueness added, of [Kolmogorov's extension theorem for projective families on Polish
spaces](../kolmogorov-extension-theorem/kolmogorov-extension.md), taken with index set $\mathbb N$ and real coordinates.

## Idea

This is how infinite sequences of random variables with prescribed finite-dimensional laws are
constructed: for instance, $\mu_n = \nu_1 \times \cdots \times \nu_n$ gives an infinite sequence of independent random
variables with laws $\nu_1, \nu_2, \dots$. Consistency only needs checking on boxes $(a_1, b_1] \times \cdots \times (a_n, b_n]$:
boxes form a π-system that generates the Borel sets, and two finite measures with the same total mass that agree on
such a π-system agree on the σ-field it generates.

## Statements

- [Kolmogorov's extension theorem for sequences](kolmogorov-extension-theorem.md)

## Background

- [Probability measures](../probability-measures/README.md): probability measures
