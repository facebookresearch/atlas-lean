# Balance distribution of the M/M/1 queue

Let $\lambda \ge 0$ be the arrival rate and $\mu > 0$ the service rate of a single server, and take
the birth–death rates on $\{0, 1, 2, \dots\}$ given by $\lambda_n = \lambda$ and $\mu_n = \mu$
($n \ge 1$). A probability distribution satisfying the balance relations
$\lambda \pi_n = \mu \pi_{n+1}$ ($n \ge 0$) exists if and only if $\lambda < \mu$, and then, with
$\rho = \lambda / \mu$, it is the geometric distribution

$$
\pi_n = (1 - \rho)\,\rho^n \qquad (n \ge 0).
$$

This is the case $s = 1$ of the balance distribution of the M/M/s queue. It describes the
solution of the balance relations only; constructing the queue-length process, showing that it
is nonexplosive and stationary under this law, and its mean queue length are separate results.

## Proof depends on

- [Balance distribution of the M/M/s queue](mms-balance-distribution.md): the case $s = 1$, where
  $1/\pi_0 = 1 + \rho/(1 - \rho) = 1/(1 - \rho)$.

## Sources

- J. Figueroa-O'Farrill, *Mathematics for Informatics 4a*, Lecture 21 (4 April 2012), University of Edinburgh, <https://webhomes.maths.ed.ac.uk/~jmf/Teaching/mi4a/Lecture21-2012.04.04.pdf>, slides 9–11 (M/M/s queues), with $s = 1$.
