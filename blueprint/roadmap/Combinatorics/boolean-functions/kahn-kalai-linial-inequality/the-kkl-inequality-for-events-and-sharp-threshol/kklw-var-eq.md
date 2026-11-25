# Variance of an event indicator is $P(A)(1 - P(A))$

Let $E$ be a finite set, $p$ a real number and $A \subseteq \{0, 1\}^E$. Under the product weights $w_p(1) = p$, $w_p(0) = 1 - p$, the [variance](../../osss-inequality-for-decision-trees/var.md) of the indicator of $A$ is

$$\mathrm{Var}_p(1_A) = P_p(A)\big(1 - P_p(A)\big),$$

where $P_p(A) = \sum_{\omega \in A} \prod_e w_p(\omega_e)$.
