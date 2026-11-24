# Independent Poisson increments of the counting process

Let $r > 0$ and let $T_0, T_1, \dots$ be independent random variables, each with the exponential
law of rate $r$, with [counting process](count.md) $N$. Let $n \in \mathbb{N}$ and
$0 \le t_0 \le t_1 \le \dots \le t_n$. Then the increments $N_{t_{i+1}} - N_{t_i}$, $i < n$, are
independent, and $N_{t_{i+1}} - N_{t_i}$ has the Poisson law of mean $r(t_{i+1} - t_i)$: the
increment vector has the product law.

## Sources

- J. F. C. Kingman, *Poisson Processes*, Oxford University Press, 1993, Chapter 4.
- S. Karlin and H. M. Taylor, *A First Course in Stochastic Processes*, 2nd ed., Academic Press,
  1975, Chapter 4.
