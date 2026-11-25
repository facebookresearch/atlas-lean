# The earliest-due-date rule minimizes maximum lateness

Consider a finite set of jobs $j$ with processing times $p_j \ge 0$, all released at time $0$, processed without preemption on one machine; $C_j$ is the completion time. For due dates $d_j$, ordering the jobs by nondecreasing $d_j$ minimizes the maximum lateness $\max_j(C_j - d_j)$, which may be negative; for an empty set of jobs the maximum is taken as $-\infty$. The proof exchanges adjacent jobs that violate the order.

## Sources

- C. Swamy (scribe D. Chakrabarty), *Scheduling Theory CO 454, Lecture 5: Single Machine Environments (Maximum Lateness)*, 2009, Definition 1.1 and Theorem 1.2, <https://www.cs.dartmouth.edu/~deepc/Courses/S09/Lectures/lecture5.pdf>
