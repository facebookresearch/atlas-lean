# Makespan

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For $m \ge 1$, the makespan of $A$, its social cost, is the maximum load
$\max_{1 \le j \le m} \ell_j(A)$ (Vöcking, *Algorithmic Game Theory*, Chapter 20, Section 20.1.1).
