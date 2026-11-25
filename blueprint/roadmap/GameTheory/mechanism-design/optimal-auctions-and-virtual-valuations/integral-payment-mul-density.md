# Myerson's revenue identity (4.10)

Let $a < b$ and let the bidder's value have a density $f : \mathbb{R} \to \mathbb{R}$ that is continuous and positive on $[a, b]$ with $\int_a^b f = 1$; write $F(t) = \int_a^t f$ and $\varphi$ for the virtual valuation. A single-parameter mechanism has an allocation rule $Q$ and a payment rule $P$ (real functions on $\mathbb{R}$), and $U(t) = t\,Q(t) - P(t)$ is the truthful utility.
If $(Q, P)$ is incentive compatible on $[a, b]$, then the expected payment is the expected virtual surplus
minus the utility of the lowest type:

$$\int_a^b P(t)\,f(t)\,dt = \int_a^b \varphi(t)\,Q(t)\,f(t)\,dt - U(a)$$

(Myerson 1981, (4.10), for one bidder without revision effects).

## Informally uses

- [Payment formula](../myerson-s-lemma-and-revenue-equivalence/payment-formula.md): the payment in terms of the allocation.
- [Virtual surplus density](virtual-value-mul-density.md): $\varphi f = t f - (1 - F)$.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, (4.10); Myerson derives it by exchanging the order of integration, and integration by parts gives the same identity.
