# Logarithmic expansions of the prime counting function

Let $\pi(x)$ be the number of
primes $p \le x$. As $x \to \infty$,

$$
\log \pi(x) = \log x - \log \log x + \frac{1}{\log x} + \frac{3}{2 (\log x)^2} +
O\left(\frac{1}{(\log x)^3}\right),
$$



$$
\log \log \pi(x) = \log \log x - \frac{\log \log x}{\log x} -
\frac{(\log \log x)^2}{2 (\log x)^2} + \frac{1}{(\log x)^2} +
O\left(\frac{(\log \log x)^3}{(\log x)^3}\right),
$$

and

$$
\frac{1}{\log \pi(x)} - \frac{1}{\log x}\left(1 + \frac{\log \log x}{\log x} +
\frac{(\log \log x)^2 - 1}{(\log x)^2} + \frac{(\log \log x)^3}{(\log x)^3}\right) =
O\left(\frac{\log \log x}{(\log x)^4}\right).
$$

The last expansion is the paper's form, whose error term $O(\log \log x / (\log x)^3)$ sits
inside the parentheses, multiplied out by the factor $1/\log x$.

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Lemma 5.
