# A failed first statement fixes the cost of a sequence

Let $f$ be a fuel, $c_1$ and $c_2$ statements and $s$ a state such that the read-counting interpreter with fuel $f$ on $c_1$ from $s$ fails. Then the read-counting interpreter with fuel $f + 1$ on $c_1 ; c_2$ from $s$ returns exactly the same pair as with fuel $f$ on $c_1$ from $s$: failure, at the cost of the run of $c_1$. The statement $c_2$ is not run, and the reads $c_1$ performed are still charged.
