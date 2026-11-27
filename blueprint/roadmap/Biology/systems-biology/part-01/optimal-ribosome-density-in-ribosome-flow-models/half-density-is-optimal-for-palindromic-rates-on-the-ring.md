# Half density is optimal for palindromic rates on the ring

**Ribosome flow model on a ring (RFMR).** For $n\ge2$ sites with occupancies $x_i(t)\in[0,1]$ and rates $\lambda_1,\dots,\lambda_n>0$, indices taken modulo $n$ (so $x_0=x_n$, $x_{n+1}=x_1$, $\lambda_0=\lambda_n$),

$$\dot x_i=\lambda_{i-1}x_{i-1}(1-x_i)-\lambda_i x_i(1-x_{i+1}),\qquad i=1,\dots,n.$$

The total density $s=\sum_i x_i$ is conserved; for each $s\in[0,n]$ the RFMR has a unique steady state $e(s)$ with $\sum_i e_i=s$, attracting all solutions on that level set, and the steady-state translation rate is $R(s)=\lambda_ie_i(1-e_{i+1})$ (the same for every $i$).

**Propositions 3 and 6.** Suppose the rates satisfy $\lambda_i=\lambda_{n-i}$ for all $i$ (indices modulo $n$). Then

- $e_i(s)=1-e_{n+1-i}(n-s)$ for all $i$ and $s$, $R(s)=R(n-s)$ for all $s\in[0,n]$, and $R$ is strictly increasing on $[0,n/2]$;
- hence the optimal total density is $s^*=n/2$, the optimal mean occupancy is $\rho^*=s^*/n=1/2$, and $e_i^*=1-e_{n+1-i}^*$.

If the condition holds only after a cyclic relabeling of the sites, the site identities hold for the relabeled indices, while $R(s)=R(n-s)$, $s^*=n/2$ and $\rho^*=1/2$, which are invariant under relabeling, hold as stated.

The condition holds automatically for $n=2$, and for $n=3$ whenever two of the three rates are equal (up to relabeling). This is the mean-field counterpart of the half-filling optimum of the homogeneous TASEP with periodic boundary conditions.

## Depends on

- [Optimal total density of the ribosome flow model on a ring](optimal-total-density-of-the-ribosome-flow-model-on-a-ring.md)

## Expansion

The particle–hole map $\bar x_i=1-x_{n+1-i}$ sends the RFMR with rates $\lambda_i$ to the RFMR with rates $\bar\lambda_i=\lambda_{n-i}$, and sends total density $s$ to $n-s$ while preserving the flow. When the rates are palindromic the two systems coincide, so $R(s)=R(n-s)$. Combining this symmetry with the unimodality of $R$ from Proposition 1 places the unique maximizer at $s=n/2$.

## Sources

- Y. Zarai, M. Margaliot, T. Tuller, "On the ribosomal density that maximizes protein translation rate", PLoS ONE 11 (2016) e0166481. <https://doi.org/10.1371/journal.pone.0166481>, PMCID PMC5115748. Propositions 3 and 6, Eq. (10).
