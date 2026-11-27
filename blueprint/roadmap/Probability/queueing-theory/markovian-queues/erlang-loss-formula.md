# Erlang's loss formula

Let $c \ge 1$ be an integer number of circuits, $\lambda \ge 0$ the arrival rate and $\mu > 0$ the
service rate, and let $\rho = \lambda / \mu$ be the offered traffic (no condition $\rho < 1$ is
needed). Take the birth–death rates on $\{0, 1, \dots, c\}$ given by $\lambda_n = \lambda$ for
$n < c$, $\lambda_c = 0$ (a call arriving when all circuits are busy is lost and changes no state)
and $\mu_n = n \mu$ for $1 \le n \le c$. The unique probability distribution satisfying the
balance relations $\lambda_n \pi_n = \mu_{n+1} \pi_{n+1}$ ($0 \le n < c$) is

$$
\pi_n = \frac{\rho^n / n!}{\sum_{k=0}^{c} \rho^k / k!} \qquad (0 \le n \le c),
$$

and its mass at the full state is Erlang's loss formula

$$
E(c, \rho) = \pi_c = \frac{\rho^c / c!}{1 + \rho + \rho^2/2! + \cdots + \rho^c / c!} .
$$

Reading $\pi_c$ as the long-run fraction of time all circuits are busy needs the corresponding
finite continuous-time Markov chain to have $\pi$ as its stationary law, and reading it as the
probability that an arriving call is lost further needs Poisson arrivals to see time averages;
neither step is part of this result.

## Proof depends on

- [Normalized balance weights of a birth–death rate sequence](../../markov-chains/birth-death-processes/birth-death-balance-weights.md):
  here $\theta_n = \rho^n / n!$ for $n \le c$ and $\theta_n = 0$ for $n > c$.

## Sources

- J. Figueroa-O'Farrill, *Mathematics for Informatics 4a*, Lecture 21 (4 April 2012), University of Edinburgh, <https://webhomes.maths.ed.ac.uk/~jmf/Teaching/mi4a/Lecture21-2012.04.04.pdf>, slides 4–6 (telecom circuits example).
