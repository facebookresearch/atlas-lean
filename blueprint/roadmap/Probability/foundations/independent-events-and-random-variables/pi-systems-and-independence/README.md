# Independence from π-systems

Let $\mu$ be a measure on $\Omega$ and, for each $i$ in an index set $\iota$, let $\pi_i$ be a π-system of subsets
of $\Omega$, closed under intersections that are nonempty, generating a σ-algebra $\mathcal M_i$ contained in that of
$\Omega$. If the π-systems are independent with respect to $\mu$, meaning that
$\mu\big(\bigcap_{j \in J} A_j\big) = \prod_{j \in J} \mu(A_j)$ for every finite $J \subseteq \iota$ and all $A_j \in \pi_j$, then
the σ-algebras $\mathcal M_i$ are independent.

## Idea

On a probability space, with $\iota = \{1, \dots, n\}$: if $\mathcal A_1, \dots, \mathcal A_n$ are independent
collections of events and each is closed under intersections, then $\sigma(\mathcal A_1), \dots, \sigma(\mathcal A_n)$ are
independent. So it is enough to check the product formula on generating π-systems. For example, real random variables
$X_1, \dots, X_n$ are independent as soon as $P(X_1 \le x_1, \dots, X_n \le x_n) = \prod_i P(X_i \le x_i)$ for all
$x_i \in (-\infty, \infty]$, because the events $\{X_i \le x\}$ form a π-system that generates $\sigma(X_i)$. The proof
is Dynkin's π–λ argument: the events that satisfy the product formula against a fixed intersection form a λ-system.
A consequence, the second statement of this card, is that Borel functions of disjoint blocks of independent real
random variables are again independent.

## Statements

- [Independent π-systems generate independent σ-algebras, for any index set](i-indep.md)
- [Functions of disjoint blocks of independent random variables](independent-disjoint-blocks-functions.md): consequence, in the real-valued form: functions of disjoint blocks of independent real random variables

## Background

- [Independence](../independence/README.md): independent collections of events

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 2.1.7, with Lemma 2.1.5 and the π–λ theorem (Theorem 2.1.6) (version read: the author's January 2019 PDF).
