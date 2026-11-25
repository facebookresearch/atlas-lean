# Smith's rule minimizes total weighted completion time

Consider a finite set of jobs $j$ with processing times $p_j \ge 0$, all released at time $0$, processed without preemption on one machine; $C_j$ is the completion time. For weights $w_j \ge 0$, putting jobs with $w_j > 0$ first, ordered so that $p_iw_j \le p_jw_i$ when $i$ precedes $j$, and jobs with $w_j = 0$ last, minimizes $\sum_jw_jC_j$; the comparison uses cross-products, never $p_j/w_j$. The proof exchanges adjacent jobs that violate the order.

## Sources

- N. Shakhlevich, *Single machine problems*, handout (after M. Pinedo, Scheduling), Theorem 1 (WSPT), <https://web-static.stern.nyu.edu/om/faculty/pinedo/scheduling/shakhlevich/handout02.pdf>
