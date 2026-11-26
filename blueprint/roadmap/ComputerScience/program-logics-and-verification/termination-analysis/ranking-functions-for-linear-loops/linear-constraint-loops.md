# Linear-constraint loops

A *single-path linear-constraint loop* (SLC loop) over $n$ variables is written

$$\mathbf{while}\ (B x \le b)\ \mathbf{do}\ A \begin{pmatrix} x \\ x' \end{pmatrix} \le c,$$

with rational matrices $B$, $A$ and rational vectors $b$, $c$. There is a *transition* from a state $x \in \mathbb{Q}^n$ to a state $x' \in \mathbb{Q}^n$ if $x$ satisfies the loop condition $Bx \le b$ and the pair satisfies the update constraint; a transition is identified with the point $x'' = (x, x') \in \mathbb{Q}^{2n}$, and the set of all transitions is the *transition polyhedron* $Q = \{x'' : A'' x'' \le c''\}$, where $A''$ stacks $(B\ 0)$ on $A$ and $c''$ stacks $b$ on $c$. The *condition polyhedron* is $C = \{x : Bx \le b\}$. A *multipath* loop (MLC loop) has finitely many alternatives, the $i$-th applicable when its condition $B_i x \le b_i$ holds, and is given by transition polyhedra $Q_1, \dots, Q_k$. The loop is *rational* when the variables range over $\mathbb{Q}$, so that its transitions are the points of the $Q_i$, and *integer* when they range over $\mathbb{Z}$, so that its transitions are the integer points $I(Q_i) = Q_i \cap \mathbb{Z}^{2n}$.

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", arXiv:1208.4041v4, 2025, <https://arxiv.org/abs/1208.4041v4>, Section 2.2.
