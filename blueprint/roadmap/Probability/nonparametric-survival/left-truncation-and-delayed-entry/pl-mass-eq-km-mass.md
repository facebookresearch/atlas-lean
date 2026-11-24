# Product-limit jumps reduce to Kaplan–Meier jumps

Consider left-truncated survival data on increasing grid times $t_0 < \dots < t_{k-1}$: subject $i$ enters at a grid index $e_i$ (or before $t_0$), leaves at $t_{x_i}$ with $e_i < x_i$, with or without an event; $d_j$ and $c_j$ are the events and censorings at $t_j$ and $Y_j = \#\{i : e_i < j \le x_i\}$ the number at risk. Suppose every entry precedes every observed exit ($e_i < x_{i'}$ for all $i, i'$). Then the delayed-entry product-limit jumps equal the Kaplan–Meier jumps of the data without entry times.
