# Prefixes of the $m$th order Gijswijt sequence

Let $m$ and $n$ be natural numbers. The
list of the first $n$ terms of the $m$th order sequence $A^{(m)}$ is defined by recursion on $n$:
for $n = 0$ it is the empty list, and the list for $n + 1$ is the list $P$ for $n$ followed by
the term $\max(m, \mathcal{C}(P))$, where $\mathcal{C}(P)$ is the curling number of $P$ (the
largest $k$ with $P = XY^k$ for strings $X$, $Y$ with $Y$ nonempty, and $1$ for the empty string).
For $m \ge 1$ the first term is therefore $A^{(m)}(1) = m$; the case $m = 1$ is Gijswijt's
sequence.

## Sources

- Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences 28 (2025), Article 25.4.6, Section 2 (definition of `A^{(m)}`).
