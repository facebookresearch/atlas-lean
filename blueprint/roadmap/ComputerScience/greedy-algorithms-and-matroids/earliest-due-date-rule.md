# The earliest-due-date rule minimizes maximum lateness

Consider a finite set of jobs $j$ with processing times $p_j \ge 0$, all released at time $0$, processed one at a time without preemption or idle time on one machine, so that a schedule is an order of the jobs; $C_j$ is the completion time, the total processing time of $j$ and of the jobs before it. For due dates $d_j$, ordering the jobs by nondecreasing $d_j$ minimizes the maximum lateness $\max_j(C_j - d_j)$ over all orders of the jobs; the lateness may be negative, and for an empty set of jobs the maximum is taken as $-\infty$. The processing times and due dates may be real numbers or, more generally, elements of any linearly ordered additive commutative group. The lecture notes prove this by exchanging adjacent jobs that violate the order.

## Sources

- D. Chakrabarty, *Lecture 5: Single Machine Environments (Maximum Lateness)*, Scheduling Theory CO 454 lecture notes, University of Waterloo, May 19, 2009, Definition 1.1 and Theorem 1.2, <https://www.cs.dartmouth.edu/~deepc/Courses/S09/Lectures/lecture5.pdf>
