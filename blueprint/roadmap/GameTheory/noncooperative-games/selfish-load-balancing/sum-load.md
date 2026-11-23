# Loads add up to the total weight

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For every assignment $A$, $\sum_{j=1}^m \ell_j(A) = \sum_{i \in I} w_i$.
