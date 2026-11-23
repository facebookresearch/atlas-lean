# Revenue bound from a single bidder

Let $a < b$ and let the bidder's value have a density $f : \mathbb{R} \to \mathbb{R}$ that is continuous and positive on $[a, b]$ with $\int_a^b f = 1$; write $F(t) = \int_a^t f$ and $\varphi$ for the virtual valuation. A single-parameter mechanism has an allocation rule $Q$ and a payment rule $P$ (real functions on $\mathbb{R}$), and $U(t) = t\,Q(t) - P(t)$ is the truthful utility.
If $(Q, P)$ is incentive compatible on $[a, b]$, $0 \le Q \le 1$ on $[a, b]$ (a probability of sale) and the
lowest type gets $U(a) \ge 0$, then the expected payment is at most the expected positive part of the
virtual surplus:

$$\int_a^b P(t)\,f(t)\,dt \le \int_a^b \max\bigl(\varphi(t)\,f(t), 0\bigr)\,dt$$

(Myerson 1981, Lemma 3 and §5 for one bidder and seller value $t_0 = 0$: selling exactly to the types with
nonnegative virtual valuation maximizes the expected virtual surplus).

## Informally uses

- [Myerson's revenue identity (4.10)](integral-payment-mul-density.md): revenue is expected virtual surplus minus $U(a)$.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, Lemma 3 and §5.
