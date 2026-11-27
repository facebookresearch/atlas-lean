# Zero-sum tuples correspond to trace-zero elements

Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for
every $a = (a_0, \dots, a_{n-1}) \in F^n$, we have $a_0 + a_1 + \dots + a_{n-1} = 0$ if and only if
the trace of $\Phi(a)$ from $K$ to $F$ is $0$.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 30 (`jis-2026-26.4.6-thm-30`).
