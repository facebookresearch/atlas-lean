# Proportion of labelled structures satisfying a sentence

For a relational language $L$ with finitely many symbols, a first-order sentence $\varphi$ over $L$
and $n \in \mathbb{N}$,

$$\mu_n(\varphi) = \frac{|\{M \text{ an } L\text{-structure on } \{1, \dots, n\} : M
\models \varphi\}|}{|\{M \text{ an } L\text{-structure on } \{1, \dots, n\}\}|}.$$

Structures are labelled: two isomorphic structures on $\{1, \dots, n\}$ count separately, so
$\mu_n$ is the probability that $\varphi$ holds in a uniformly random structure on $n$ labelled
elements. Both counts are finite and the denominator is positive.

## Background

- [Finitely many structures on a finite set](finite-structure.md): the counts are finite.
- [Relational languages have structures on every type](nonempty-structure.md): the denominator
  is positive.

## Sources

- P. G. Kolaitis and M. Y. Vardi, "0-1 laws for fragments of existential second-order logic: a survey", MFCS 2000, LNCS 1893, Springer 2000, pp. 84-98, Section 1 (author's posted version, https://www.cs.rice.edu/~vardi/papers/mfcs00i.pdf).
