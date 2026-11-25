# Strong law of large numbers from the ergodic theorem

Let $(S, p)$ be a probability space and $g : S \to \mathbb{R}$ a $p$-integrable function. For
$p^{\mathbb{N}}$-almost every sequence $x = (x_0, x_1, \dots)$,

$$\frac{1}{n} \sum_{k=0}^{n-1} g(x_k) \longrightarrow \int_S g \, dp \qquad (n \to \infty).$$

This is the strong law of large numbers for independent identically distributed random variables, obtained
from dynamics. Under $p^{\mathbb{N}}$ the coordinates are i.i.d. with law $p$, and along the
[Bernoulli shift](../mixing/shift.md) the Birkhoff averages of $g(x_0)$ are exactly the empirical means
([Birkhoff averages along the Bernoulli shift are empirical means](birkhoff-average-shift-eval-zero.md)).
Since the [Bernoulli shift is ergodic](../mixing/ergodic-shift.md), the Birkhoff pointwise ergodic theorem
identifies the limit with the space average. In this sense the ergodic theorem is the law of large numbers
for stationary processes: Birkhoff's theorem "extends the validity of the strong law to stationary sequences"
(Lalley), and Koralov and Sinai's textbook develops ergodic theory as a chapter on strictly stationary
processes. The strong law also has direct probabilistic proofs, such as Etemadi's for pairwise independent
identically distributed variables.

## Background

- [Strong law of large numbers](../../../Probability/laws-of-large-numbers/strong-law-of-large-numbers/README.md):
  the probabilistic proofs of the strong law.

## Sources

- S. Lalley, *Birkhoff's ergodic theorem*, lecture notes for Statistics 381, University of Chicago,
  https://galton.uchicago.edu/~lalley/Courses/381/Birkhoff.pdf, introduction.
- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Proposition 1.7 (Bernoulli schemes are mixing, whence ergodic).
- Leonid B. Koralov and Yakov G. Sinai, *Theory of Probability and Random Processes*, 2nd ed., Universitext,
  Springer (2007), Chapter 16 (Strictly Stationary Random Processes; chapter title checked, content not consulted).
