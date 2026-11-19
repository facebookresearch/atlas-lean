# Cardinality bounds of generic chaining

$N_0 = 1$ and $N_n = 2^{2^n}$ for $n \ge 1$ (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, (2.29)). They satisfy $N_n^2 \le N_{n+1}$, and
$\sqrt{\log N_n}$ is of order $2^{n/2}$, which is where the weights $2^{n/2}$ of $\gamma_2$ come
from: a union bound over $N_n$ sub-Gaussian variables costs a factor $\sqrt{\log N_n}$.
