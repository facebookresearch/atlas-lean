# Mallows metric of sums in a Hilbert space

Let $E$ be a separable real Hilbert space and let $\mu_1, \nu_1, \mu_2, \nu_2$ be probability measures on $E$ with finite second moments. If $\mu_2$ and $\nu_2$ have the same mean, then

$$d_2(\mu_1 * \mu_2, \nu_1 * \nu_2)^2 \le d_2(\mu_1, \nu_1)^2 + d_2(\mu_2, \nu_2)^2 .$$

Here $d_2^2$ is the optimal transport cost of order $2$.

Bickel and Freedman state the lemma for $m$ summands and assume $E(U_j) = E(V_j)$ for every $j$. The statement above has two summands and assumes equality of means for the second pair only. For couplings $\pi_1, \pi_2$ and $a(x, y) = x - y$, the independent coupling of the two pairs has cost

$$\int \|a(z_1) + a(z_2)\|^2 \, d(\pi_1 \otimes \pi_2) = \int \|a\|^2 \, d\pi_1 + \int \|a\|^2 \, d\pi_2 + 2 \Bigl\langle \int a \, d\pi_1, \int a \, d\pi_2 \Bigr\rangle,$$

and the cross term vanishes as soon as one mean displacement $\int a \, d\pi_j$ is zero. For $p = 2$ this improves the triangle-type bound [Mallows metric of sums of independent variables](wasserstein-conv-le.md).

## Informally uses

- [Coupling of convolutions](is-coupling-conv.md): "the same construction as in the previous lemma", the independent coupling of the two pairs.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.7.
