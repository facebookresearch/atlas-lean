# Mean absolute sum over the unit cube

For $n \in \mathbb{N}$ let

$$I_n = \int_{[-1/2,\, 1/2]^n} \left| \sum_{i=1}^n x_i \right| dx,$$

the integral with respect to Lebesgue measure on the cube. Then $I_n / \sqrt{n} \to 1 / \sqrt{6\pi}$
as $n \to \infty$.

## Idea

Read probabilistically, $I_n = \mathbb{E}|U_1 + \dots + U_n|$ for independent random variables $U_i$
uniform on $[-1/2, 1/2]$, each with mean $0$ and variance $1/12$. By the central limit theorem,
$(U_1 + \dots + U_n)/\sqrt{n}$ converges in law to $N(0, 1/12)$, and $\mathbb{E}|Z| = \sigma\sqrt{2/\pi}$
for $Z$ with law $N(0, \sigma^2)$, which gives $\sqrt{1/12}\,\sqrt{2/\pi} = 1/\sqrt{6\pi}$. To pass from
convergence in law to convergence of the means, note that the second moment of
$(U_1 + \dots + U_n)/\sqrt{n}$ is $1/12$ for $n > 0$, so the absolute values are uniformly integrable.
The statement is a concrete case of the central limit theorem evaluating a high-dimensional integral.

## Statements

- [Mean absolute sum over the unit cube](tendsto-integral-abs-sum-cube-div-sqrt.md)

## Background

- [Lindeberg–Feller central limit theorem](../lindeberg-feller-central-limit-theorem/README.md): the
  central limit theorem used in the argument.
