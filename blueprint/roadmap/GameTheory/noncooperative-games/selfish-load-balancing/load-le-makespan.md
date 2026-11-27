# Every load is at most the makespan

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For $m \ge 1$, every load is at most the makespan: $\ell_j(A) \le \max_k \ell_k(A)$ for every machine $j$.
