# Normalized balance weights of a birth–death rate sequence

Let $(\lambda_n)_{n \ge 0}$ be real birth rates with $\lambda_n \ge 0$ and $(\mu_n)_{n \ge 1}$ real
death rates with $\mu_n > 0$, indexed by $n \in \{0, 1, 2, \dots\}$. Put

$$
\theta_0 = 1, \qquad \theta_n = \frac{\lambda_0 \lambda_1 \cdots \lambda_{n-1}}{\mu_1 \mu_2 \cdots \mu_n} \quad (n \ge 1).
$$

A probability distribution $(\pi_n)_{n \ge 0}$ on $\{0, 1, 2, \dots\}$ satisfies the balance
relations

$$
\lambda_n \pi_n = \mu_{n+1} \pi_{n+1} \qquad (n \ge 0)
$$

if and only if the series $S = \sum_{n \ge 0} \theta_n$ converges and $\pi_n = \theta_n / S$ for every
$n$. In particular such a distribution is unique when it exists. If some $\lambda_k = 0$, then
$\theta_n = 0$ for all $n > k$, the series reduces to a finite sum and the distribution always
exists.

This is a statement about the balance relations only. It constructs no birth–death process and
makes no claim that a process with these rates is nonexplosive, recurrent, stationary under this
distribution or convergent to it: for infinitely many states, summability of $(\theta_n)$ alone
does not imply those properties.

## Sources

- J. Figueroa-O'Farrill, *Mathematics for Informatics 4a*, Lecture 21 (4 April 2012), University of Edinburgh, <https://webhomes.maths.ed.ac.uk/~jmf/Teaching/mi4a/Lecture21-2012.04.04.pdf>, slides 2–3 (zero net flow condition and steady-state probabilities).
