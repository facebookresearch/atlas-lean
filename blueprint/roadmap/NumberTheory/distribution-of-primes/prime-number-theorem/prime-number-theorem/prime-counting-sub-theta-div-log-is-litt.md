# Prime counting versus theta over log

Let $\pi(x)$ be the number of primes $p \le x$ and
let $\theta(x) = \sum_{p \le x} \log p$, the sum running over primes. As the real number $x$ tends
to $+\infty$,

$$\pi(x) - \frac{\theta(x)}{\log x} = o\left(\frac{x}{\log x}\right).$$

The proof upgrades the bound $\pi(x) - \theta(x)/\log x = O(x/(\log x)^2)$, using that
$x/(\log x)^2 = o(x/\log x)$.
