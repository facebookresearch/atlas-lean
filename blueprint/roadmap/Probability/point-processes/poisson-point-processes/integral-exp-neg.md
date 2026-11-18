# Laplace functional

Let $\mu$ be a finite measure on a measurable space $E$, let $\eta$ be distributed as the
[Poisson point process](poisson-point-process.md) with intensity $\mu$, and let
$f : E \to [0, \infty)$ be measurable. Then

$$\mathbb{E}\Big[\exp\Big(-\int f \, d\eta\Big)\Big] = \exp\Big(-\int \big(1 - e^{-f}\big)\, d\mu\Big).$$

For every configuration charged by the process, $\int f \, d\eta$ is a finite sum
$\sum_i f(x_i)$.

## Sources

- G. Last and M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press, 2017, Theorem 3.9.
