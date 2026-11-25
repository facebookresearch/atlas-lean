# Independence

Events, random variables and σ-fields on a probability space are independent when probabilities of
intersections factor. σ-fields $\mathcal F_1, \dots, \mathcal F_n$ are independent if
$P(A_1 \cap \dots \cap A_n) = \prod_i P(A_i)$ whenever $A_i \in \mathcal F_i$; random variables $X_1, \dots, X_n$ if
$P(X_1 \in B_1, \dots, X_n \in B_n) = \prod_i P(X_i \in B_i)$ for all Borel sets $B_i$; events $A_1, \dots, A_n$ if
$P\big(\bigcap_{i \in I} A_i\big) = \prod_{i \in I} P(A_i)$ for every set $I$ of indices; and collections
$\mathcal A_1, \dots, \mathcal A_n$ of events if the same product formula holds for every set $I$ of indices and every
choice of $A_i \in \mathcal A_i$, so that one-element collections give independent events. An infinite family is
independent if each of its finite subfamilies is.

## Idea

The notions are nested: random variables are independent exactly when the σ-fields they generate are,
and events exactly when their indicator functions are. Independence of a family is stronger than pairwise
independence: for two independent fair signs $\xi_1, \xi_2 \in \{-1, 1\}$, the events $\{\xi_1 = 1\}$, $\{\xi_2 = 1\}$
and $\{\xi_1 \xi_2 = 1\}$ are pairwise independent, but the probability that all three occur is $\frac14$, not
$\frac18$.

## Statements

- [Independence of σ-fields, random variables and events](independence-sigma-fields.md)

## Background

- [Probability measures](../../probability-measures/README.md): probability spaces
