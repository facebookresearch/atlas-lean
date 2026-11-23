# Crişan–Erban expansion of the semiprime counting function

A semiprime is a product of
exactly two primes counted with multiplicity; for real $x$ let $N_2(x)$ be the number of semiprimes
at most $x$. Let $\beta$ be the Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni constant
and $\log$ the natural logarithm. There are real constants $c_0, c_1, c_2, \dots$ with
$c_0 = \beta$ and

$$
c_1 = \beta - 1 - \gamma - \sum_{p} \frac{\log p}{p (p - 1)},
$$

the sum running over all primes $p$, such that for every natural number $N$, as $x \to \infty$,

$$
N_2(x) = \frac{x}{\log x} \sum_{n=0}^{N-1} \frac{n! \, (\log \log x + c_n)}{\log^n x} +
O_N\left( \frac{x \log \log x}{\log^{N+1} x} \right).
$$

The paper calls the $c_n$ explicit but displays only $c_0$ and $c_1$; the remaining constants are
only asserted to exist.

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Lemma 1 (quoting Crişan and Erban).
