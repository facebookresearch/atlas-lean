# Thinning

Let $P$ be a probability measure on $\Omega$, let $N$ be a [Poisson process](is-poisson-process.md)
of rate $r \ge 0$, and let $p \in [0, 1]$. Let $B_0, B_1, \dots$ be independent measurable marks
with values in $\{\text{true}, \text{false}\}$ and $P(B_i = \text{true}) = p$ for every $i$, and
suppose that the path $(N_t)_{t \ge 0}$ is independent of the sequence $(B_i)_{i \ge 0}$. Then the
[thinning](thinning.md) of $N$ by the marks $B$ is a Poisson process of rate $pr$: keeping each
point of $N$ independently with probability $p$ gives a Poisson process of rate $pr$.

## Sources

- J. F. C. Kingman, *Poisson Processes*, Oxford University Press, 1993, Section 5.1.
- S. Karlin and H. M. Taylor, *A First Course in Stochastic Processes*, 2nd ed., Academic Press,
  1975, Chapter 4, Section 1.
