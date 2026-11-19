# General prime sieve for the line problem

Let $q$ and $n$ be natural numbers, let $\omega$
be the number of distinct prime factors of $q^n - 1$, and let $S$ and $T$ be disjoint sets of prime
factors of $q^n - 1$, with $s = |S|$ and $r = |T|$. Let $k$ be the product of the prime factors of
$q^n - 1$ that lie in neither $S$ nor $T$, and put $\delta = 1 - \sum_{\rho \in S} 1/\rho$,
$\varepsilon = \sum_{l \in T} 1/l$ and $\mu = \varphi(k)/k$, where $\varphi$ is Euler's totient
function. Suppose that $\delta\mu > \varepsilon$ and

$$
q > (n - 1)^2 \left(\frac{2^{\omega - s - r} \mu (s - 1 + 2\delta) - \delta\mu + r -
\varepsilon}{\delta\mu - \varepsilon}\right)^2.
$$

Then for all finite fields $K$ and $L$ with $L$ an extension of $K$, $|K| = q$ and $[L : K] = n$,
and all nonzero $\gamma_1, \gamma_2 \in L$ with $K(\gamma_1/\gamma_2) = L$, there is $a \in K$
such that $a\gamma_2 + \gamma_1$ generates the multiplicative group $L^\times$.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 7, quoting Bailey, Cohen, Sutherland and Trudgian, Lemma 1.
