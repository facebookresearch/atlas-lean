# Jordan decomposition of continuous functions of bounded variation

Let $F : \mathbb{R} \to \mathbb{R}$ be continuous and of bounded variation on all of $\mathbb{R}$.
Then $F = F_1 - F_2$ for continuous non-decreasing functions $F_1, F_2 : \mathbb{R} \to \mathbb{R}$.

## Idea

A function of bounded variation moves up and down by a finite total amount, and the decomposition
separates the upward from the downward motion. Take $F_1(x)$ to be the total variation of $F$ on
$(-\infty, x]$ and $F_2 = F_1 - F$; both are non-decreasing, and continuity of $F$ makes the
variation function continuous. The decomposition reduces functions of bounded variation to
monotone ones: by Lebesgue's theorem they are differentiable almost everywhere, and
$F(x) - \lim_{y \to -\infty} F(y) = \nu((-\infty, x])$ for a finite signed measure $\nu$ on the
line.

## Statements

- [Jordan decomposition of a continuous function of bounded variation](exists-continuous-monotone-sub-of-bounde.md)

## Background

- [Functions of bounded variation](../bounded-variation-and-total-variation/README.md): the definition, applied on $\mathbb{R}$
