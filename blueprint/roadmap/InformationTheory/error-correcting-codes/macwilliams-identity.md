# MacWilliams identity

Let $C \subseteq \mathbb{F}_q^n$ be a linear code, $C^\perp$ its dual under the standard bilinear form
$\langle u, v \rangle = \sum_i u_i v_i$, and $W_C(x, y) = \sum_{c \in C} x^{n - \mathrm{wt}(c)} y^{\mathrm{wt}(c)} \in \mathbb{Z}[x, y]$ its weight
enumerator. Then, as an identity of polynomials with rational coefficients,
$W_{C^\perp}(x, y) = \frac{1}{\lvert C \rvert} W_C(x + (q-1)y,\ x - y)$.

## Proof

Fix a nontrivial additive character $\chi$ of $\mathbb{F}_q$, for example $\chi(a) = e^{2\pi i \operatorname{Tr}(a)/p}$ with $p$ the
characteristic and $\operatorname{Tr}$ the absolute trace onto $\mathbb{F}_p$. For $u \in \mathbb{F}_q^n$ let
$f(u) = x^{n - \mathrm{wt}(u)} y^{\mathrm{wt}(u)}$ and $\hat f(v) = \sum_{u} \chi(\langle u, v \rangle) f(u)$. The sum factors over
coordinates, and $\sum_{a \in \mathbb{F}_q} \chi(a v_i)\, x^{[a = 0]} y^{[a \ne 0]}$ is $x + (q-1)y$ if $v_i = 0$ and $x - y$ otherwise,
since $\sum_{a \ne 0} \chi(a b) = -1$ for $b \ne 0$. Hence $\hat f(v) = (x + (q-1)y)^{n - \mathrm{wt}(v)} (x - y)^{\mathrm{wt}(v)}$. For fixed $u$,
$v \mapsto \chi(\langle u, v \rangle)$ is a character of the group $C$, trivial exactly when $u \in C^\perp$, because a nonzero
linear functional on $C$ is onto $\mathbb{F}_q$. So $\sum_{v \in C} \chi(\langle u, v \rangle)$ is $\lvert C \rvert$ for $u \in C^\perp$ and $0$
otherwise, and
$\sum_{v \in C} \hat f(v) = \sum_u f(u) \sum_{v \in C} \chi(\langle u, v \rangle) = \lvert C \rvert\, W_{C^\perp}(x, y)$, while the left side is
$W_C(x + (q-1)y,\ x - y)$.

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Dual code](linear-codes/dual.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory* (draft), Exercise 2.36 (the binary case, as an exercise
  based on the identity proved by F. J. MacWilliams, Bell System Technical Journal 42 (1963), 79–94); the $q$-ary
  identity is derived above.
  <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/ada-coding-book.pdf>
