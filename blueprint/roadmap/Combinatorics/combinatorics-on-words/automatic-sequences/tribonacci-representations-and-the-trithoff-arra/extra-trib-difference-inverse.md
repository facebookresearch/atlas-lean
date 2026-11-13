# Difference-inverses of extraTribs

Let $S$ be an extraTrib. There is exactly one
sequence $Q \colon \mathbb{Z} \to \mathbb{Q}$ that follows the Tribonacci rule
$Q(n+3) = Q(n+2) + Q(n+1) + Q(n)$ for all $n \in \mathbb{Z}$ and satisfies
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$. Moreover, there is an extraTrib $Q$ with
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$ if and only if $S$ is not of Type EEOO
(parities repeating even, even, odd, odd), that is, there is no integer $k$ such that for
every $n \in \mathbb{Z}$, $S(n)$ is even exactly when $(n - k) \bmod 4$ is $0$ or $1$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Theorem 9 (`jis-2025-25.5.4-thm-9`).
