# One step of the sparse-table construction

Work over a type with a minimum operation
$\min$. Given a pair $(r, L)$ of a current row $r$ (an array of length $|r|$) and an array $L$
of the rows recorded so far, and a natural number $k$, the build step returns the pair
$(r', L')$, where $L'$ is $L$ with $r$ appended at the end, and $r'$ is the array whose
entry $i$ is $\min(r_i, r_{i+2^k})$ for each $i$ with $i + 2^k < |r|$.
