# Factorial effects from ±1 coding in a balanced two-level design

In a full two-level experiment with $k$ factors and $r\ge 1$ replicates of each treatment, let $N=r2^k$ be the total number of runs. Code the two levels as $-1$ and $+1$. The column indexed by a factor subset is the product of its factors' codes. The empty subset gives the intercept, and the remaining $2^k-1$ subsets give the main effects and interactions.

Writing $X$ for the [design matrix](factorial-design.md), the columns are mutually orthogonal and $X^{\mathsf T}X=NI$. Thus the ordinary least-squares estimate is the unique minimizer of the residual sum of squares, and its intercept coefficient is the grand mean. Each other column takes the values $+1$ and $-1$ on exactly $N/2$ runs each. Its least-squares coefficient is $(\bar y_+-\bar y_-)/2$, where $\bar y_+$ and $\bar y_-$ are the mean responses in the respective groups of runs. The conventional factorial effect is $\bar y_+-\bar y_-$, twice that coefficient.

## Sources

- The statement is derived from the product coding and the least-squares normal equations.
