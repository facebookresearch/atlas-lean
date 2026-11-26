# Linear system for first-order weak-selection fixation probabilities

Suppose the weak-selection derivatives of the marginal replacement probabilities $e_{ji}(x)$ are
multilinear polynomials of degree at most $D$ in $x \in \mathbb{B}^N$:
$$\left.\frac{d}{d\delta} e_{ji}(x)\right|_{\delta=0} = \sum_{I \subseteq \{1,\dots,N\},\, |I| \le D} c_I^{ji} x_I, \qquad x_I := \prod_{k \in I} x_k.$$
For any fixed initial configuration $\xi \in \mathbb{B}^N$, the fixation probability of allele $A$ satisfies
$$\rho_A(\xi) = \hat\xi + \delta \sum_{i=1}^N \pi_i \sum_{j=1}^N \sum_{I \subseteq \{1,\dots,N\},\, |I| \le D} c_I^{ji} \bigl(\eta_{\{i\} \cup I}^\xi - \eta_{\{j\} \cup I}^\xi\bigr) + O(\delta^2),$$
where $\eta_I^\xi := \langle \hat x - x_I \rangle_\xi^\circ$ is the unique solution to the finite linear system
$$\eta_I^\xi = \hat\xi - \xi_I + \sum_{(R,\alpha)} p^\circ(R, \alpha)\, \eta_{\tilde\alpha(I)}^\xi \quad (1 \le |I| \le D + 1), \qquad \sum_{i=1}^N \pi_i \eta_{\{i\}}^\xi = 0,$$
with $\tilde\alpha(i) = \alpha(i)$ for $i \in R$ and $\tilde\alpha(i) = i$ otherwise.

## Depends on

- [First-order weak-selection expansion of fixation probability](weak-selection-fixation-probability-expansion.md)

## Expansion

Substituting the multilinear expansion of $\frac{d}{d\delta} e_{ji}(x)|_{\delta=0}$ into
$\widehat\Delta_{\mathrm{sel}}(x) = \sum_{i,j} \pi_i e_{ji}(x)(x_j - x_i)$ expresses the
first-order term in Theorem 1 as a linear combination of $\eta_I^\xi = \langle \hat x - x_I \rangle_\xi^\circ$
over subsets $I$ of size at most $D+1$. Applying the neutral one-step recurrence for $\langle \cdot \rangle_\xi^\circ$
yields the closed linear system for $\eta_I^\xi$, whose solution is unique because the neutral
coalescing lineage process reaches size $1$ almost surely and $\sum_i \pi_i \eta_{\{i\}}^\xi = 0$.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01567-5>. (Theorem 2.)
