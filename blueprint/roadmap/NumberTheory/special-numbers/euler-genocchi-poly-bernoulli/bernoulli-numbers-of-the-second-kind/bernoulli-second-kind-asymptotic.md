# Asymptotic expansion of the Bernoulli numbers of the second kind

For a natural number
$n$ let $b_n = \frac{1}{n!} \int_0^1 x (x - 1) \cdots (x - n + 1) dx$, and for a natural
number $k$ let $\beta_k$ be $(-1)^k$ times the $(k + 1)$-th derivative of $1 / \Gamma$ at $0$.
Then for every natural number $m$, as $n \to \infty$,

$$b_n - \frac{(-1)^{n+1}}{n (\log n)^2} \sum_{k=0}^{m} \frac{\beta_k}{(\log n)^k} =
o\left(\frac{1}{n (\log n)^{m+2}}\right).$$

The main term $(-1)^{n+1} / (n (\log n)^2)$ is Steffensen's approximation, as noted in the
source.

## Sources

- Gergő Nemes, "An Asymptotic Expansion for the Bernoulli Numbers of the Second Kind," Journal of Integer Sequences 14 (2011), Article 11.4.8, Theorem (label theorem), equations (eq1)–(eq2), lines 124–133, https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex
