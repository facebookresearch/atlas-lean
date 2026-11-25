# Linear combinations of geometric solutions at characteristic roots

Let $R$ be a commutative ring and let $E$ be the linear recurrence of order $d$ with coefficients $c_0, \dots, c_{d-1} \in R$, whose solutions are the sequences $u \colon \mathbb{N} \to R$ with $u_{n+d} = \sum_{i<d} c_i\,u_{n+i}$ for all $n$, and whose characteristic polynomial is $X^d - \sum_{i<d} c_i X^i$. Let $s$ be a finite index set and $a_i, r_i \in R$ for $i \in s$, with every $r_i$ a root of the characteristic polynomial. Then the sequence

$$n \mapsto \sum_{i \in s} a_i\,r_i^{\,n}$$

is a solution of $E$ (with $0^0 = 1$, so a root $r_i = 0$ contributes $a_i$ at $n = 0$ only).
