# Absolute-deviation minimizers of a sample are the median interval

Let $n \ge 1$ and let $x_{(1)} \le \dots \le x_{(n)}$ be the order statistics of real numbers $x_1, \dots, x_n$ (ties allowed). The function $f(m) = \sum_i |x_i - m|$ attains its minimum exactly on the closed interval $[x_{(\lceil n/2 \rceil)},\ x_{(\lfloor n/2 \rfloor + 1)}]$. For odd $n$ this is the single point $x_{((n+1)/2)}$; for even $n$ it is the interval between the two middle order statistics, a single point when they are equal. Proof: $f$ is convex and piecewise linear, and on an open interval containing no $x_i$ its slope is the number of $x_i$ below minus the number above, which is negative to the left of $x_{(\lceil n/2 \rceil)}$, positive to the right of $x_{(\lfloor n/2 \rfloor + 1)}$ and zero strictly between them. For $n = 0$ the sum is empty and every real number minimizes it, so the sample median is undefined.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
