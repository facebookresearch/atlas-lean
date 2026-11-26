# Kolmogorov–Chentsov tightness criterion in $C([0,T])$

Let $T>0$ and, for each $n$, let $X^n=(X^n_t)_{t\in[0,T]}$ be a real process with continuous paths, so that its law is a Borel probability measure on $C([0,T])$ with the uniform norm. Suppose that

1. the laws of $X^n_0$, $n\ge1$, are tight;
2. there are constants $\alpha,\beta,C>0$ such that for all $n$ and all $s,t\in[0,T]$

$$\mathbb E\,\bigl\lvert X^n_t-X^n_s\bigr\rvert^{\alpha}\le C\,\lvert t-s\rvert^{1+\beta}.$$

Then the laws of $X^n$, $n\ge1$, are tight in $C([0,T])$.

## Depends on

- [Tight family of probability measures](tightness-of-probability-measures/is-tight-family.md)

## Expansion

A proof page must establish, from the moment bound and a chaining argument over the dyadic points of $[0,T]$, a bound on the modulus of continuity uniform in $n$: for every $\eta>0$, $\lim_{\delta\to0}\sup_n\mathbb P\bigl(w(X^n,\delta)\ge\eta\bigr)=0$, where $w(x,\delta)=\sup_{\lvert t-s\rvert\le\delta}\lvert x(t)-x(s)\rvert$; and conclude with the Arzelà–Ascoli characterization of relatively compact subsets of $C([0,T])$, which together with the tightness of the initial values gives a compact set of uniformly large probability.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Chapter 2, Section 4.
- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 2.
