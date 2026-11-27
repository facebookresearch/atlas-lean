# Pythagorean identity for linear families

Let $Q > 0$ on a finite alphabet, $f_i : \alpha \to \mathbb R$ and $c_i \in \mathbb R$ for $i$ in any index
type, and let $\mathcal L = \{P \ge 0 : \sum_a P(a) = 1,\ \sum_a P(a) f_i(a) = c_i \ \forall i\}$. If
$P^* \in \mathcal L$ minimises $D(\cdot\|Q)$ over $\mathcal L$, then

$$D(P\|Q) = D(P\|P^*) + D(P^*\|Q) \qquad \text{for every } P \in \mathcal L.$$

$\mathcal L$ is convex and, because $P^*$ has the largest support in $\mathcal L$, $P^*$ is an algebraic
inner point of it, so the [identity at an inner point](pythagorean-identity-at-an-inner-point.md)
applies. This is the first assertion of the tutorial's Theorem 3.2; its second assertion
($\mathcal L \cap \mathrm{cl}(\mathcal E_Q) = \{P^*\}$, the exponential-family form of $P^*$) is not part of the statement.
The index type of the constraints is arbitrary, a mild generalisation of the source's $k$ functions.

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Theorem 3.2 (first assertion) and the definition of a linear family preceding it.
