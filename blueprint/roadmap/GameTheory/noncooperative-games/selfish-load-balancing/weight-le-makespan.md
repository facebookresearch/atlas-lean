# A single task bounds every makespan

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For $m \ge 1$ and nonnegative weights, $w_i \le \max_j \ell_j(B)$ for every task $i$ and every assignment
$B$.
