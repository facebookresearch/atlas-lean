# Rows of Pascal's triangle are log-concave

For every $n$ the sequence $\binom{n}{0}, \binom{n}{1}, \dots, \binom{n}{n}$ is log-concave:

$$\binom{n}{k} \binom{n}{k+2} \le \binom{n}{k+1}^2 .$$

Proof sketch: from $\binom{n}{j+1}(j+1) = \binom{n}{j}(n-j)$, multiplying
$\binom{n}{k}\binom{n}{k+2}$ by $(n-k)(k+2)$ gives $\binom{n}{k+1}^2 (k+1)(n-k-1)$, which is at most
$\binom{n}{k+1}^2 (n-k)(k+2)$. Equivalently, the ratio
$\binom{n}{k+1} / \binom{n}{k} = (n - k)/(k + 1)$ decreases with $k$.

Newton's theorem (Exercise 50(b)) is a different, stronger kind of statement: for a real-rooted
polynomial $\sum_i \binom{n}{i} b_i x^i$ the normalised sequence $(b_i)$ is log-concave. Together with
this lemma it gives log-concavity of the coefficients of real-rooted polynomials with nonnegative
coefficients.

## Sources

- Richard P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Chapter 1, Exercise 50, for the definition of log-concavity and, in part (b), Newton's theorem.
