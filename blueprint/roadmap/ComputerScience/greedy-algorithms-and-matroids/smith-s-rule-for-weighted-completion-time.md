# Smith's rule minimizes total weighted completion time

Consider finitely many jobs $j$ with real processing times $p_j \ge 0$ and real weights $w_j \ge 0$, all released at time $0$ and processed on one machine without preemption. A schedule is an order of the jobs: a list in which every job occurs exactly once. The machine processes the jobs one after another in that order from time $0$, without idle time, so the completion time $C_j$ of job $j$ is the sum of $p_i$ over the jobs $i$ up to and including $j$. Smith's rule asks that, whenever job $i$ precedes job $j$, $w_j > 0$ implies $w_i > 0$, so that the jobs with $w_j > 0$ come first and those with $w_j = 0$ last, and $p_iw_j \le p_jw_i$; the comparison uses cross-products, never $p_j/w_j$. Some schedule follows Smith's rule, and every schedule that follows it minimizes $\sum_jw_jC_j$ over all schedules.

The proof exchanges adjacent jobs that violate the order: exchanging adjacent jobs $a$ and $b$, so that $b$ moves ahead of $a$, changes $\sum_jw_jC_j$ by $w_ap_b - w_bp_a$.

## Sources

- N. Shakhlevich, *Scheduling: Models and Algorithms*, School of Computing, University of Leeds, 2004/2005, Handout 2, "Single machine problems", Theorem 1 (the WSPT rule), p. 3, <https://web-static.stern.nyu.edu/om/faculty/pinedo/scheduling/shakhlevich/handout02.pdf>. The handout states the rule with the ratios $p_j/w_j$.
