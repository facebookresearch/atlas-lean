# Polynomial triangle removal holds in $\mathbb{F}_2^n$

There are real constants $c > 0$
and $C > 0$ such that for every natural number $n$, every finite set $A \subseteq \mathbb{F}_2^n$
and every real number $\varepsilon$ with $0 < \varepsilon \le 1$ the following holds: if every
triangle-free $B \subseteq A$ misses at least $\varepsilon 2^n$ elements of $A$, then the
triangle count of $A$ is at least $c \varepsilon^C 4^n$. Here a set $B \subseteq \mathbb{F}_2^n$
is triangle-free when there are no $x, y \in B$ with $x + y \in B$ (the case $x = y$ is allowed),
and the triangle count of $A$ is the number of ordered pairs $(x, y) \in A \times A$ with
$x + y \in A$, so that it divided by $4^n$ is the probability that $x, y, x + y \in A$ for
independent uniform $x, y \in \mathbb{F}_2^n$.

This answers O'Donnell's Problem 14 in the affirmative. Fox and Lovász proved it with the
essentially tight exponent $C = 1 + 1/(5/3 - \log_2 3) \approx 13.239$.

## Sources

- R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447, Problem 14 (Triangle Removal in 𝔽₂ⁿ); resolution: J. Fox and L. M. Lovász, A tight bound for Green's arithmetic triangle removal lemma in vector spaces, Adv. Math. 321 (2017), 287-297, arXiv:1606.01230, Theorem 1: for 0 < ε < 1 and δ = (ε/3)^{C_p}, if X, Y, Z ⊆ 𝔽_pⁿ span fewer than δ N² triangles (N = pⁿ) then removing εN elements of X ∪ Y ∪ Z kills all triangles; C₂ = 1 + 1/(5/3 - log₂ 3) ≈ 13.239 (applied with X = Y = Z = A and p = 2; the case ε = 1 follows from ε < 1), https://arxiv.org/abs/1606.01230.
