# Differentiating an integral of a series term by term

Let $d \in \mathbb{N}$, let $\Omega$
be an open subset of $\mathbb{R}^d$, let $a < c < b$ be real numbers, and for each
$n \in \mathbb{N}$ let $f_n : \mathbb{R}^d \times \mathbb{R} \to \mathbb{C}$ be almost everywhere
measurable on $\Omega \times (a, b)$ with respect to Lebesgue measure. Write
$\partial_y f_n(x, y)$ for the derivative of $t \mapsto f_n(x, t)$ at $y$, taken to be $0$ where
this derivative does not exist, and give every series that does not converge absolutely the
sum $0$. Assume that:
(1) for each $n$ and almost every $x \in \Omega$, the function $y \mapsto f_n(x, y)$ is
absolutely continuous on $[a, b]$;
(2) each $\partial_y f_n$ is almost everywhere measurable on $\Omega \times (a, b)$, the series
$\sum_n |\partial_y f_n(x, y)|$ converges for almost every $(x, y) \in \Omega \times (a, b)$,
and its sum is integrable on $\Omega \times (a, b)$;
(3) the series $\sum_n |f_n(x, c)|$ converges for almost every $x \in \Omega$, and its sum is
integrable on $\Omega$.
Then there is a function $F : \mathbb{R} \to \mathbb{C}$ such that for almost every
$y \in (a, b)$ the function $x \mapsto \sum_n f_n(x, y)$ is integrable on $\Omega$,
$F(y) = \int_\Omega \sum_n f_n(x, y)\, dx$, and $F$ is differentiable at $y$ with

$$
F'(y) = \sum_n \int_\Omega \partial_y f_n(x, y)\, dx.
$$

The joint measurability of each $f_n$ is a hypothesis of the source that the first formalization
dropped. It is needed: for $d \ge 1$ and nonempty bounded $\Omega$, a non-measurable $f_0$ of
modulus one that does not depend on $y$, with $f_n = 0$ for $n \ge 1$, satisfies the other
hypotheses but not the conclusion.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), problem `ma_proofbench_l2_50`, with the change above.
