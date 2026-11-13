# Asymptotics of power-logarithm sums

For all $m, n, k \in \mathbb{N}$, as the natural
number $x$ tends to infinity,

$$\sum_{\ell=1}^{x} \ell^m (\log \ell)^n \sim \frac{x^{m+1} (\log x)^n}{m+1}$$

and

$$\sum_{\ell=1}^{x} \frac{\ell^m (\log \ell)^n}{(\log \log \ell)^k} \sim
\frac{x^{m+1} (\log x)^n}{(m+1)(\log \log x)^k}.$$

In the second sum the term $\ell = 1$, where $\log \log 1 = \log 0$ is undefined, is evaluated with
the conventions $\log 0 = 0$ and $t/0 = 0$; a single term does not affect the asymptotic.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Lemma 9 (`jis-2024-24.4.1-lem-9`).
