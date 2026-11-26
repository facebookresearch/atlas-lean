# `≤` is not a partial order with NaN

Let $F$ be a binary format and let $a \le b$ mean that
$a$ compares less than or equal to $b$. Then $\mathrm{NaN} \le \mathrm{NaN}$ fails, so $\le$ is not
reflexive, and hence not a partial order on the values of $F$.

## Sources

- Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Sections 3.2.2 (NaNs are unordered) and 2.3.1 (comparisons with a NaN return false).
