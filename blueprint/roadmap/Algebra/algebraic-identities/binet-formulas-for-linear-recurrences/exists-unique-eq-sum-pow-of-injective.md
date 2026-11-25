# Closed form for linear recurrences with distinct characteristic roots

Let $K$ be a field and $E$ a linear recurrence over $K$ of order $d$ with coefficients $c_0, \dots, c_{d-1}$ (solutions: $u_{n+d} = \sum_{i<d} c_i u_{n+i}$ for all $n$). Suppose $r_0, \dots, r_{d-1} \in K$ are pairwise distinct roots of the characteristic polynomial $X^d - \sum_{i<d} c_i X^i$. Then every solution $u \colon \mathbb{N} \to K$ has exactly one expression

$$u_n = \sum_{i=0}^{d-1} a_i\,r_i^{\,n} \quad (n \in \mathbb{N})$$

with coefficients $a_0, \dots, a_{d-1} \in K$. Here $0^0 = 1$, so one of the roots may be $0$; for $d = 0$ the only solution is the zero sequence and the coefficient family is empty. No assumption on the characteristic of $K$ is needed.
