# Payment formula

A single-parameter mechanism is given by an allocation rule $Q : \mathbb{R} \to \mathbb{R}$ and a payment rule $P : \mathbb{R} \to \mathbb{R}$: an agent of value $t$ who reports $s$ gets the utility $t\,Q(s) - P(s)$, and $U(t) = t\,Q(t) - P(t)$ is its truthful utility.
If $(Q, P)$ is incentive compatible on $[a, b]$, the payment is determined by the allocation rule and the
utility of the lowest value: for every $t \in [a, b]$,

$$P(t) = t\,Q(t) - \int_a^t Q(x)\,dx - U(a)$$

(Myerson 1981, (4.8) with $U(a) = 0$; Hartline and Karlin 2007, Theorem 13.6 (ii), where $a = 0$ and
$P(0) = 0$).

## Informally uses

- [Envelope formula](envelope-formula.md): solved for the payment.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, (4.8).
- J. D. Hartline and A. R. Karlin, "Profit maximization in mechanism design", Chapter 13 of the same volume, Theorem 13.6 (ii).
