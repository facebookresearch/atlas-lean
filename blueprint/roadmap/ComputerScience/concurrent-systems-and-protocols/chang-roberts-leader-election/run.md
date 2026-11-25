# Running a delivery schedule

Given a natural-number identifier $\mathrm{id}(k)$ for each
process $k$ of the ring, a global state $s$ and a list $k_1, \dots, k_r$ of processes, the run
applies the Chang–Roberts delivery step at $k_1$, then at $k_2$, and so on. It returns the final
state, or no state as soon as some $k_i$ has an empty channel at its turn; on the empty list it
returns $s$.
