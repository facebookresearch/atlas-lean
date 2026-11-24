# Recurrence for power-weighted sums of hypersequences

Let $a$ be a sequence of complex
numbers, let $a^{(r)}_k$ denote its hypersequence of generation $r$, and for natural numbers
$\ell$, $r$ and $n$ let $t^{(r)}_\ell(n) = \sum_{k=0}^{n} k^\ell a^{(r)}_k$, with the convention
$0^0 = 1$. Then for all natural numbers $\ell$, $r$ and $n$,

$$t^{(r)}_\ell(n) = (n + 1)^\ell a^{(r+1)}_n - \sum_{j=0}^{\ell-1} \binom{\ell}{j} t^{(r+1)}_j(n),$$

where the sum over $j$ is empty when $\ell = 0$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 8, Equation (3.5).
