# Nested sums of reciprocal odd squares

For every natural number $k$,

$$\sum_{i_1 \ge i_2 \ge \cdots \ge i_k \ge 1} \prod_{j=1}^{k} \frac{1}{(2 i_j - 1)^2} =
\frac{(\pi/2)^{2k} E^*_{2k}}{(2k)!},$$

where the sum runs over all weakly decreasing $k$-tuples $(i_1, \ldots, i_k)$ of positive integers
and $E^*_{2k} = \sec^{(2k)}(0)$ is the $2k$-th derivative at $0$ of $\sec x = 1/\cos x$ (the Euler
zig number, OEIS A000364). For $k = 0$ the sum has the single empty term and both sides equal $1$.

The source also claims that the sum equals $(\pi/4)\,\beta(2k+1)$, where $\beta$ is Dirichlet's beta
function; this is false as printed and is not stated here: at $k = 0$ the sum is $1$ but
$(\pi/4)\,\beta(1) = \pi^2/16$, and at $k = 1$ it is $\pi^2/8$ but $(\pi/4)\,\beta(3) = \pi^4/128$
(the correct factor is $4/\pi$).

## Sources

- Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26 (2026), Article A114, Theorem 1.
