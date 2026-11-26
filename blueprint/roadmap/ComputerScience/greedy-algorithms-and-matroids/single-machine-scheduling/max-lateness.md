# Maximum lateness on a single machine

Let finitely many jobs $j$ have processing times
$p_j$ and due dates $d_j$ in an additive commutative group with a linear order, such as
$\mathbb{Z}$ or $\mathbb{R}$. The maximum lateness of a list $\sigma$ of jobs is
$L_{\max} = \max_j (C_j - d_j)$ over all jobs $j$, where $C_j$ is the completion time of job $j$
when the machine processes the jobs of $\sigma$ one after another from time $0$. The lateness
$C_j - d_j$ is negative when job $j$ completes before its due date. The maximum is taken in
`WithBot`, so that it is `⊥`, standing for $-\infty$, when there are no jobs.
