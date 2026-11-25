# Large level sets under a reverse Hölder bound

Let $\mu$ be Lebesgue measure on $[0, 1]$ and $f_0, f_1, \ldots$ functions in $L^2(\mu)$ with
$\|f_n\|_{L^2(\mu)} \le 2024 \, \|f_n\|_{L^1(\mu)}$ for every $n$ and
$\|f_n\|_{L^1(\mu)} \to \infty$. Then there are real numbers $y_n \to \infty$ with

$$\inf_n \mu(\{x : |f_n(x)| \ge y_n\}) > 0.$$

## Idea

A reverse Hölder bound $\|f\|_2 \le C \|f\|_1$ says that $f$ is not concentrated on a small set.
The Paley–Zygmund inequality makes this quantitative: on a probability space,
$\mu\{|f| \ge \|f\|_1 / 2\} \ge \frac{1}{4} \|f\|_1^2 / \|f\|_2^2 \ge 1 / (4 C^2)$. This needs
$\|f\|_1 > 0$. Taking $y_n = \|f_n\|_1 / 2$, which tends to infinity, gives level sets of measure at
least $1/(4C^2)$; for the finitely many $n$ with $\|f_n\|_1 = 0$, $y_n = 0$ and the level set is all
of $[0, 1]$.

## Statements

- [Uniformly large level sets under a reverse Hölder bound](exists-tendsto-at-top-inf-measure-level.md)
- [Lebesgue measure on the unit interval](icc01.md): the measure of the statement.
