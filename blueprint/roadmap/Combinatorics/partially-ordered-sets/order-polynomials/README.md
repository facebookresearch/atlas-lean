# Order polynomials

The order polynomial $\Omega_P(m)$ of a finite poset $P$ counts the order-preserving maps
$P \to \{1, \dots, m\}$; equivalently, after reversing $[m]$, the $P$-partitions of a naturally
labelled $P$ with parts at most $m$. It is a polynomial in $m$ of degree $|P|$ whose leading
coefficient is $e(P)/|P|!$, with $e(P)$ the number of linear extensions, and it satisfies the
reciprocity $\bar\Omega_P(m) = (-1)^{|P|}\, \Omega_P(-m)$ with the count of strictly order-preserving
maps. Order polynomials, $P$-partitions and their reciprocity go back to Stanley's thesis
*Ordered structures and partitions* (1971); *Enumerative Combinatorics*, vol. 1, Sections 3.12 and
3.15, is the standard reference.

- [Order polynomial](order-polynomial-value.md)
- [Strict order polynomial](strict-order-polynomial-value.md)
- [Surjective order-preserving maps](surj-monotone-count.md)
- [Surjective order-preserving maps onto $[p]$ are linear extensions](surj-monotone-count-card-eq.md)
- [Order polynomial at one](order-polynomial-value-one.md)
- [No surjection onto a larger chain](surj-monotone-count-eq-zero.md)
- [Order-preserving maps with a given image](image-equiv.md)
- [Grouping order-preserving maps by their image](order-polynomial-value-eq-sum-finset.md)
- [Expansion of the order polynomial in binomial coefficients](order-polynomial-value-eq-sum.md)
- [The order polynomial is a polynomial](exists-order-polynomial.md)
- [Reciprocity theorem for order polynomials](order-polynomial-reciprocity.md)

## Related topics

- [Linear extensions of posets](../linear-extensions-of-posets/README.md): $e(P)$, the number of
  linear extensions, is $|P|!$ times the leading coefficient of $\Omega_P$.
- [Neggers–Stanley conjecture](../neggers-stanley-conjecture/README.md): for a nonempty naturally labelled $P$, $\sum_{m \ge 0} \Omega_P(m) x^m = x\, W(P, x) / (1 - x)^{|P| + 1}$, where $W(P, x)$ is the
  $W$-polynomial $\sum_w x^{\mathrm{des}(w)}$ over linear extensions (EC1, Theorem 3.15.8).
