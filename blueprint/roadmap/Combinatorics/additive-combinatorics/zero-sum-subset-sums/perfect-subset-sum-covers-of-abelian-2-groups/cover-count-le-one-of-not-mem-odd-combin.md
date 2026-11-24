# Distinct subset sums from the odd-combination condition

Let $G$ be an abelian group,
and for a finite set $A \subseteq G$ write $\mathcal{T}(A)$ for the set of odd combinations of
$A$. Let $x = (x_1, \dots, x_m)$ be a family in $G$ such that
$x_i \notin \mathcal{T}(\{x_1, \dots, x_{i-1}\})$ for every $i$ (for $i = 1$ this says
$x_1 \ne 0$, and for $i \ge 2$ it forces $x_i \ne 0$). Then $x$ covers every element of $G$ at
most once, that is, all subset sums of $x$ are distinct; if moreover $|G| = 2^m$, then $x$ is a
perfect $1$-cover of $G$.

## Sources

- John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 16 (`jis-2025-25.7.8-lem-16`). The paper's "nonzero" hypothesis is the case $i = 1$ of the odd-combination condition; distinctness needs no finiteness of $G$, and the paper's "$m = n$" is $|G| = 2^m$.
