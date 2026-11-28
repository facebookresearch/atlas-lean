# Maximum lateness on a single machine

Let finitely many jobs $j$ have processing times
$p_j$ and due dates $d_j$ in an additive commutative group with a linear order, such as
$\mathbb{Z}$ or $\mathbb{R}$. The maximum lateness of a list $\sigma$ of jobs is
$L_{\max} = \max_j (C_j - d_j)$ over all jobs $j$, where $C_j$ is the completion time of job $j$
when the machine processes the jobs of $\sigma$ one after another from time $0$. The list need
not be a schedule: a repeated job completes at its first occurrence in $\sigma$, and a job that
does not occur in $\sigma$ is given the total processing time of $\sigma$ as its completion time
and still counts in the maximum. When the order is compatible with addition, as in $\mathbb{Z}$
or $\mathbb{R}$, a job that completes before its due date has negative lateness $C_j - d_j$. The
maximum is taken in `WithBot`, so that it is `⊥`, standing for $-\infty$, when there are no
jobs.
