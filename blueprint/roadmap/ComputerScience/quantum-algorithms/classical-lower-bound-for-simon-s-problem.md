# Classical lower bound for Simon's problem

For a positive integer $n$, let $f:\{0,1\}^n\to\{0,1\}^n$ satisfy the promise
$f(x)=f(y)$ if and only if $y\in\{x,x\oplus s\}$, for an unknown nonzero string
$s\in\{0,1\}^n$. One classical oracle query chooses an input $x$ and receives the entire $n$-bit value
$f(x)$. A randomized query algorithm is a distribution over adaptive deterministic oracle algorithms,
chosen independently of $f$; its query bound is the maximum number of queries over its possible executions.

Every such algorithm that returns $s$ with probability at least $2/3$ for every promised input requires
$\Omega(2^{n/2})$ queries in the worst case as $n\to\infty$. This counts whole-value classical queries,
not ordinary operations or coherent quantum queries.

## Depends on

- [Adaptive oracle algorithms](../cryptography/security-games/oracle-algorithms/oracle-comp.md)
- [Query bound](../cryptography/security-games/oracle-algorithms/is-query-bounded.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §3.1 (promise and whole-value oracle queries) and §3.3.2 (classical lower bound). <https://arxiv.org/pdf/1907.09415v6>
