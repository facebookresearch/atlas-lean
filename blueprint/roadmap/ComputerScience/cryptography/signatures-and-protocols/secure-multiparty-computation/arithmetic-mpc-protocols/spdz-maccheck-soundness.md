# Soundness of the SPDZ batch MAC check

In SPDZ over a prime field $\mathbb{F}_p$, linear operations and Beaver multiplication on authenticated shares preserve the authentication invariant $\sum_i \gamma_i = \alpha \sum_i x_i$. If the adversary opens values $x'_1, \dots, x'_t$ of which at least one differs from the authenticated value, the batch MACCheck with public uniform coefficients $r_1, \dots, r_t$ and the commit-then-open of the $\sigma_i$ accepts with probability at most $2/p$, where the probability is over the uniform MAC key (unknown to the adversary) and the coefficients.

## Proof sketch

Acceptance requires $\alpha \sum_j r_j \delta_j = \Delta$ for the adversary's errors $\delta_j$ and a correction $\Delta$ chosen before $\alpha$ is used: the combination $\sum_j r_j \delta_j$ is zero with probability at most $1/p$, and otherwise the equation fixes $\alpha$, which is uniform and hidden, so it holds with probability $1/p$.

## Depends on

- [SPDZ authenticated secret sharing](spdz-authenticated-sharing.md)

## Sources

- Ivan Damgaard et al., "Practical Covertly Secure MPC for Dishonest Majority –- Or: Breaking the SPDZ Limits", Computer Security –- ESORICS 2013, 2013.
- Ivan Damgaard, Valerio Pastro, Nigel P. Smart and Sarah Zakarias, "Multiparty Computation from Somewhat Homomorphic Encryption", Advances in Cryptology –- CRYPTO 2012, 2012.
