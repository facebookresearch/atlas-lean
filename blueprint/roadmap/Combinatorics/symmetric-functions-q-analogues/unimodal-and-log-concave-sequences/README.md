# Unimodal and log-concave sequences

A finite sequence $(a_0, \dots, a_n)$ is unimodal if it weakly rises to a peak and then weakly
falls, and log-concave if $a_i^2 \ge a_{i-1} a_{i+1}$. Many sequences of combinatorics (binomial
and Gaussian binomial coefficients, Stirling numbers, $h$-vectors, coefficients of characteristic
polynomials of matroids) have these properties. For nonnegative sequences without internal zeros,
log-concavity implies unimodality, and a real-rooted generating polynomial implies log-concavity
(Newton). Richard P. Stanley, *Enumerative Combinatorics*, Vol. 1, 2nd ed., Cambridge University
Press, 2012, Chapter 1, Exercise 50, collects the basic facts; his survey "Log-concave and unimodal
sequences in algebra, combinatorics, and geometry", Annals of the New York Academy of Sciences 576
(1989), 500–535, develops the methods.

## Definitions

- [Unimodal sequence](is-unimodal.md)
- [Log-concave sequence](is-log-concave.md)
- [Sequence with no internal zeros](no-internal-zeros.md)

## Results

- [Log-concave implies unimodal](is-unimodal-of-is-log-concave.md)
- [Rows of Pascal's triangle are log-concave](choose-is-log-concave.md)
- [Rows of Pascal's triangle are unimodal](choose-is-unimodal.md)
- [Products of symmetric unimodal polynomials](symmetric-unimodal-mul.md)
- [Products of log-concave polynomials](log-concave-mul.md)

## Related topics

- [Real-rooted polynomials](../../../Algebra/zeros-of-polynomials/real-rooted-polynomials/README.md):
  real-rootedness of the generating polynomial is the strongest of the three properties and the
  usual way to prove log-concavity.
- [Gaussian binomial coefficients](../gaussian-binomial-coefficients/README.md): the coefficients of
  $\binom{m+n}{m}_q$ are symmetric and unimodal (Richard P. Stanley, *Topics in Algebraic Combinatorics*, author's draft of 1 February 2013, Corollary 6.10, <https://math.mit.edu/~rstan/algcomb/algcomb.pdf>)
  but not log-concave in general: $\binom{4}{2}_q = 1 + q + 2q^2 + q^3 + q^4$.
- [Neggers–Stanley conjecture](../../partially-ordered-sets/neggers-stanley-conjecture/README.md):
  a real-rootedness conjecture for $W$-polynomials of posets, now refuted; real-rootedness would
  have implied that their coefficients are log-concave and unimodal.
