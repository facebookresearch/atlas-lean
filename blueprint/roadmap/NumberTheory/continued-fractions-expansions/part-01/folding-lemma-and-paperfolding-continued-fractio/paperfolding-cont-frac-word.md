# Continued-fraction words of the paperfolding sums

For a sequence $x = (x_k)_{k \ge 0}$ of
natural numbers, the finite words $A_k$ of natural numbers are defined by $A_0 = (1, 1)$ and
$A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$: the concatenation of $A_k$, the single letter
$\max(x_{k+1} - 1, 0)$ and the mirror image $A_k^r$ of $A_k$. The mirror image of a word reverses
it and then replaces a leading $2$ by $1, 1$, or two leading letters $1, 1$ by $2$, leaving any
other word unchanged.

## Sources

- Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15.
