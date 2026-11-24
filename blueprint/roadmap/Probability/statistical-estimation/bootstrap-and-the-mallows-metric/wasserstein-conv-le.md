# Mallows metric of sums of independent variables

Let $1 \le p < \infty$ and let $\mu_1, \nu_1, \mu_2, \nu_2$ be Borel probability measures on a separable normed abelian group. Then

$$d_p(\mu_1 * \mu_2, \nu_1 * \nu_2) \le d_p(\mu_1, \nu_1) + d_p(\mu_2, \nu_2),$$

where $d_p = W_p$ is the Mallows (Wasserstein) metric and $*$ is convolution. In terms of random variables: if $U_1, U_2$ are independent and $V_1, V_2$ are independent, then $d_p(U_1 + U_2, V_1 + V_2) \le d_p(U_1, V_1) + d_p(U_2, V_2)$.

Bickel and Freedman state the inequality for $m$ summands; the statement above is the case of two summands, from which the general case follows by induction. No moment assumption is needed, since $d_p$ takes values in $[0, \infty]$.

The proof couples the two pairs independently and applies Minkowski's inequality in $L^p$ of the product coupling. Taking infima over the two couplings gives the claim without using that the infimum is attained (Bickel and Freedman start from optimal couplings, their Lemma 8.1).

## Informally uses

- [Coupling of convolutions](is-coupling-conv.md): the independent coupling of the pairs $(U_j, V_j)$, the construction of Bickel and Freedman's proof.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.6.
