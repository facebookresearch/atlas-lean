# Running a computation on a random tape

Let $h(a, r)$ be an answer to the query $a$ computed from a tape entry $r$. Running an oracle
computation on a tape $(r_1, r_2, \dots)$ answers its $i$-th query $a$ with $h(a, r_i)$, using a
fixed default entry once the tape is used up, and returns its output. The run is deterministic.
