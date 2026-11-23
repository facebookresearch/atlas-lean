# Exponential approximation of the divisor-counting function

Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. For a natural number $n$ let $\tau(n)$ be the number
of positive divisors of $n$ and

$$\tilde\tau(n) = \sum_{k=1}^{n} e^{-nkA(k, n)\sin^2(n\pi/k)}.$$

Then $\tilde\tau(n) - \tau(n) = O\left(\frac{1}{e^n - 1}\right)$ as $n \to \infty$.

## Sources

- Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 2.
