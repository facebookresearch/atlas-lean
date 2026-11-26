# Short integer solutions exist when $\beta \ge \sqrt{m}\, q^{n/m}$

Let $q \ge 1$, $n \ge 0$, $m \ge 1$, and let $\beta \ge \sqrt{m}\, q^{n/m}$ be real. Then every matrix $A \in \mathbb{Z}_q^{n \times m}$ admits a nonzero integer vector $z \in \mathbb{Z}^m$ with $A z \equiv 0 \pmod q$ and $\|z\|_2 \le \beta$. In particular, for such parameters $\ell_2$-SIS always has a solution.

## Proof sketch

Let $t = \lfloor q^{n/m} \rfloor$ and consider the $(t+1)^m > q^n$ vectors of $\{0, 1, \dots, t\}^m$. By the pigeonhole principle two distinct ones $x \ne y$ have $A x \equiv A y \pmod q$, so $z = x - y$ is nonzero, lies in $\Lambda_q^\perp(A)$, and has $|z_i| \le t$, hence $\|z\|_2 \le \sqrt m\, t \le \beta$.

## Depends on

- [The short integer solution problem in the Euclidean norm](sis-euclidean-norm.md)

## Sources

- Daniele Micciancio and Oded Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing, 2007.
