# Formulas for the Lehmer bounds

Let $L(t; r)$ and $U(t; r)$ be the lower and upper
Lehmer bounds of a list $t$ of real numbers, and write $\emptyset$ for the empty list. Then
$L(\emptyset; r) = 1$ for every $r \ge 1$, and $U(\emptyset; r) = 2^r - 1$ for every natural
number $r$. Let $t = (t_1, \dots, t_s)$ with $s \ge 1$ and $2 \le t_1 \le \dots \le t_s$, and
let $r \ge s$ be a natural number. Then

$$U(t; r) = \frac{t_1 \cdots t_{s-1} t_s^{r-s+1} - 1}
{(t_1 - 1) \cdots (t_{s-1} - 1)(t_s - 1)^{r-s+1}},$$

and if moreover $r > s$, then

$$L(t; r) = \frac{t_1 \cdots t_s}{(t_1 - 1) \cdots (t_s - 1)}.$$

The condition $r > s$ for $L$ is needed: for $s = r$ the only admissible completion of $t$ is the
empty list, so $L(t; r) = \kappa_r(t)$, where $\kappa_r$ is the Lehmer function; for $t = (2)$
and $r = 1$ this is $\kappa_1(2) = 1$, while the formula gives $2$. Likewise
$L(\emptyset; 0) = \kappa_0 = 0$.

## Sources

- Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026), Article A33, Lemma 1.
