# Asynchronous iteration of monotone mappings

In the [totally asynchronous iteration model](the-totally-asynchronous-iteration-model.md), let $f$ be monotone ($x \le x'$ coordinatewise implies $f(x) \le f(x')$) and let $\underline x \le \bar x$ in $X$ be such that the box $\{x : \underline x \le x \le \bar x\}$ lies in $X$, $f^k(\underline x) \le f^{k+1}(\underline x) \le f^{k+1}(\bar x) \le f^k(\bar x)$ for all $k$, and $\lim_k f^k(\underline x) = \lim_k f^k(\bar x) = x^*$ coordinatewise, a fixed point of $f$. Then the sets $X^k = \{x : f^k(\underline x) \le x \le f^k(\bar x)\}$ satisfy the conditions of the [asynchronous convergence theorem](the-asynchronous-convergence-theorem.md), so the asynchronous iteration converges to $x^*$ from every initial state with all buffers in the box $[\underline x, \bar x]$.

## Depends on

- [The asynchronous convergence theorem](the-asynchronous-convergence-theorem.md)

## Sources

- D. P. Bertsekas, "Distributed asynchronous computation of fixed points", *Mathematical Programming* 27:107–120, 1983; <https://web.mit.edu/dimitrib/OldFiles/www/Distr_Comp_Fixed.pdf>, Section 4.3 (monotone mappings, conditions (25)–(28)).
