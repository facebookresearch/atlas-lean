# Itô integral of an elementary integrand

For an [elementary integrand](elementary-integrand.md) $H$ with times $t_i$ and coefficients $\xi_i$, and a real
process $B$, the Itô integral of $H$ against $B$ is the process

$$t \mapsto \sum_i \xi_i \bigl( B_{\min(t_{i+1}, t)} - B_{\min(t_i, t)} \bigr), \qquad t \ge 0 .$$

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.A.
