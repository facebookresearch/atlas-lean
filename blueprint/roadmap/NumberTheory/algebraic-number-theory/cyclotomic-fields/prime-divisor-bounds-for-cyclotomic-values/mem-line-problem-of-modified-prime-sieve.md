# Cohen's modified prime sieve for the line problem

Let $q$ and $n$ be natural numbers such
that $q^n - 1$ has $\omega \ge 2$ distinct prime factors. Let $S$ be a set of $s$ prime factors of
$q^n - 1$, let $l$ be a prime factor of $q^n - 1$ not in $S$, let $k$ be the product of the prime
factors of $q^n - 1$ that are neither $l$ nor in $S$, and put
$\delta = 1 - \sum_{\rho \in S} 1/\rho$. Suppose that $\delta > 1/(l\varphi(k))$, where $\varphi$ is
Euler's totient function, and

$$
q > (n - 1)^2 \left(\frac{2^{\omega - s - 1} \varphi(k) (s - 1 + 2\delta) + 1 - 1/l}
{\varphi(k)\delta - 1/l} - 1\right)^2.
$$

Then for all finite fields $K$ and $L$ with $L$ an extension of $K$, $|K| = q$ and $[L : K] = n$,
and all nonzero $\gamma_1, \gamma_2 \in L$ with $K(\gamma_1/\gamma_2) = L$, there is $a \in K$
such that $a\gamma_2 + \gamma_1$ generates the multiplicative group $L^\times$.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 6, quoting S. D. Cohen, Proposition 6.3.
