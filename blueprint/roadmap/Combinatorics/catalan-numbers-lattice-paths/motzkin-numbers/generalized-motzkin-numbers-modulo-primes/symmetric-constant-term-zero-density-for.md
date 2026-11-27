# Zero density of shifted combinations of central trinomial coefficients

Let $\alpha$ and
$\beta$ be integers with $\alpha \neq 0$, and write $a_r$ for the generalized central trinomial
coefficient with parameters $\alpha, \beta$, the constant term of
$(\alpha x^{-1} + \beta + \alpha x)^r$. Let $p$ be a prime, let $h < p$ be a natural number, let
$(c_i)_{i \ge 0}$ be a sequence of integers, and set $b_r = \sum_{i=0}^{h} c_i a_{r+i}$ for
$r \in \mathbb{N}$. Suppose that $a_r \not\equiv 0 \pmod p$ for every $r \in \mathbb{N}$. For
$p - h \le r \le p - 1$ put $C_r = \min(h, p - r - 1)$, $S_r = \sum_{i=0}^{C_r} c_i a_{r+i}$ and
$S'_r = \sum_{i=C_r+1}^{h} c_i a_{i-(p-r)}$. Let $N_0$ be the number of $r$ with $0 \le r < p - h$
and $b_r \equiv 0 \pmod p$, let $N_1$ be the number of pairs $(r, m)$ with $p - h \le r \le p - 1$
and $0 \le m \le p - 2$ such that $a_m S_r \equiv -a_{m+1} S'_r \pmod p$, and let $N_2$ be the
number of pairs $(r, m)$ in that range such that $a_m S_r \equiv -a_{p-1} a_{m+1} S'_r \pmod p$.
Then the set of $r \in \mathbb{N}$ with $b_r \equiv 0 \pmod p$ has natural density

$$\frac{N_0}{p} + \frac{N_1}{(p-1)(p+1)} + \frac{N_2}{(p-1)p(p+1)}.$$

No assumption $p > 2$ is made.

## Sources

- Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 2.
