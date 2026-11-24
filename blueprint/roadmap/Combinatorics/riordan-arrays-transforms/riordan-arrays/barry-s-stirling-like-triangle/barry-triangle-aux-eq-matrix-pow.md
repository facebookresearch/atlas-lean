# Matrix power formula for Barry's triangle

Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Let $M$ be the $(a - 1) \times (a - 1)$ lower bidiagonal matrix of natural
numbers with diagonal entries $M_{i,i} = i(a - i)$ for $i = 1, \dots, a - 1$, entries
$M_{i+1,i} = 1$ just below the diagonal, and all other entries $0$. Then $s(0, n, a)$ is the
bottom-left entry $(M^{n-2})_{a-1,1}$ of the power $M^{n-2}$.

## Sources

- Bulat Khaidarov, [*Enumeration of Certain k-Block Partitions of Barry*](https://cs.uwaterloo.ca/journals/JIS/VOL29/Khaidarov/khai3.pdf), Journal of Integer Sequences 29 (2026), Article 26.2.8, equation (4), taking the last entry of the resulting vector. Equation (7) gives an individual shifted-diagonal term in the expansion of that matrix power.
