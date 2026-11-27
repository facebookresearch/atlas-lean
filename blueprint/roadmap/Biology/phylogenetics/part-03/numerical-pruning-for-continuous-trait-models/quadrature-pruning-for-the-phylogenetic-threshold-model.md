# Quadrature pruning for the phylogenetic threshold model

**Partial likelihoods.** Let $T$ be a rooted binary tree with $n$ tips, branch lengths $t_i$, trait transition densities $f(x_i \mid x_j,\theta_i)$ from parent $j$ to child $i$, root density $f(x\mid\theta_r)$, and observation probabilities $\pi(z_i \mid x_i)$ at the tips. For a non-root node $i$ with parent $j$, the partial likelihood $F_i(x_j)$ of the data below $i$ given the parent's value satisfies

$$F_i(x_j) = \int f(\tilde x\mid x_j,\theta_i)\,\pi(z_i\mid\tilde x)\,d\tilde x \ \ (\text{tip}),\qquad F_i(x_j) = \int f(\tilde x\mid x_j,\theta_i)\,F_u(\tilde x)F_v(\tilde x)\,d\tilde x\ \ (\text{children } u,v),$$

and the likelihood is $L(T) = \int f(x\mid\theta_r)F_u(x)F_v(x)\,dx$ over the root's children. With the top-down recursion $G_r \equiv 1$, $G_i(x) = \int f(\tilde x\mid x,\theta_i)\,G_j(\tilde x)\,F_u(\tilde x)\,d\tilde x$ ($u$ the sibling of $i$, $f(\tilde x\mid x,\theta_i)$ the parent-given-child density), the marginal posterior at node $i$ with children $u,v$ is

$$f(x_i\mid z_1,\dots,z_n) = \frac{G_i(x_i)\,F_u(x_i)\,F_v(x_i)\,f(x_i)}{L(T)}.$$

**Threshold model.** The liability is Gaussian at the root, $\phi(x\mid\mu_r,\sigma_r^2)$, evolves by Brownian motion, $f(x_i\mid x_j) = \phi(x_i\mid x_j,\sigma^2 t_i)$, and each tip records $z_i = 1$ if $x_i > 0$, $z_i = 0$ if $x_i \le 0$, or missing. The marginal prior of node $i$ is $N(\mu_r, v_i)$ with $v_i = \sigma_r^2 + \sigma^2\sum_{j\in P_i} t_j$ over the root-to-$i$ path $P_i$. Truncate node $i$'s integrals to $[L_i,U_i]$ with $L_i = \Phi^{-1}\big(\tfrac{\epsilon}{2(n-1)}\mid\mu_r,v_i\big)$ and $U_i$ the symmetric upper quantile, and evaluate each integral by Simpson's rule on $N+1$ grid points $X_i[0..N]$, storing $F_i[k] \approx F_i(X_j[k])$.

**Theorem.** This algorithm computes the threshold-model likelihood in $O(nN^2)$ time with error $O(nN^{-4})$, taking $\epsilon = nN^{-4}$.

## Depends on

- [Felsenstein's pruning algorithm computes the likelihood conditioned on the root state](../../felsenstein-s-pruning-algorithm/prune-eq-brute-lik.md)

## Proof depends on

- [Error of the composite Simpson rule](../../../../Analysis/numerical-analysis/numerical-quadrature/composite-simpson-rule-error.md)

## Expansion

Conditional independence of disjoint subtrees gives the recursion, exactly as in discrete pruning; the only change is that states range over $\mathbb R$, so each node stores its partial likelihood at $N+1$ points and each of the $O(nN)$ stored values costs one $O(N)$ quadrature. Simpson's rule converges as $O(N^{-4})$ for integrands with bounded fourth derivatives; the Gaussian transition densities are smooth and, by induction on the recursion, the fourth derivative of $F_i$ is $O(n_i)$ with $n_i$ the number of tips below $i$, so quadrature errors accumulate additively to $O(nN^{-4})$. The quantile truncation puts total tail mass at most $\epsilon$ outside the integration boxes. The same scheme applies to other non-Gaussian trait models (for example Ornstein–Uhlenbeck processes with discretized observations), though non-reversible processes need the reverse transition density in the $G$ recursion; for sharply peaked integrands, approximating only the non-Gaussian factor by piecewise quadratics (a Gaussian-kernel rule) improves accuracy.

## Sources

- G. Hiscott, C. Fox, M. Parry, D. Bryant, "Efficient recycled algorithms for quantitative trait models on phylogenies", Genome Biology and Evolution 8:1338–1350 (2016), Eqs (10)–(29), (37)–(39), Algorithm 1 and Theorem 1, <https://doi.org/10.1093/gbe/evw064>, PMCID PMC4898791.
