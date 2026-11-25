# Balance distribution of the M/M/s queue

Let $s \ge 1$ be an integer number of servers, $\lambda \ge 0$ the arrival rate and $\mu > 0$ the service
rate of each server, and take the birth–death rates on $\{0, 1, 2, \dots\}$ given by
$\lambda_n = \lambda$ and $\mu_n = \min(n, s)\,\mu$ ($n \ge 1$). A probability distribution
satisfying the balance relations $\lambda_n \pi_n = \mu_{n+1} \pi_{n+1}$ ($n \ge 0$) exists if and
only if $\lambda < s \mu$, and it is then unique. In that case, with $\rho = \lambda / (s \mu)$,

$$
\pi_n =
\begin{cases}
\pi_0 \, \dfrac{(s\rho)^n}{n!}, & 0 \le n \le s, \\[2mm]
\pi_0 \, \dfrac{s^s \rho^n}{s!}, & n \ge s,
\end{cases}
\qquad
\frac{1}{\pi_0} = \sum_{k=0}^{s-1} \frac{(s\rho)^k}{k!} + \frac{(s\rho)^s}{s!\,(1 - \rho)} .
$$

The two formulas agree at $n = s$. This describes the solution of the balance relations only; the
queue-length process, its stationarity and the waiting-time (Erlang C) quantities are separate
results.

## Proof depends on

- [Normalized balance weights of a birth–death rate sequence](../../markov-chains/birth-death-processes/birth-death-balance-weights.md):
  here $\theta_n = (s\rho)^n / n!$ for $n \le s$ and $\theta_n = s^s \rho^n / s!$ for $n \ge s$. The
  tail from $n = s$ is geometric with ratio $\rho$, so $\sum_n \theta_n$ converges exactly when
  $\rho < 1$ (for $\lambda > 0$ it diverges when $\rho \ge 1$; $\lambda = 0$ gives $\rho = 0$).

## Sources

- J. Figueroa-O'Farrill, *Mathematics for Informatics 4a*, Lecture 21 (4 April 2012), University of Edinburgh, <https://webhomes.maths.ed.ac.uk/~jmf/Teaching/mi4a/Lecture21-2012.04.04.pdf>, slides 9–11 (M/M/s queues). The normalizing constant above is obtained by summing the
  geometric tail in the unsimplified expression of slides 10–11.
