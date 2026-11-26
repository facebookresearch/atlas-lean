# Rate and distance of left-right Cayley complex codes

Let $X = \mathrm{Cay}^2(A, G, B)$ with $|A| = |B| = \Delta$, both Cayley graphs $\lambda$-spectral expanders, and let $C_A, C_B \subseteq \mathbb{F}_2^{\Delta}$ have rates $\rho_A, \rho_B$ and relative distances $\delta_A, \delta_B$. Then the code $C = C[G, A, B, C_A, C_B]$ of length $N = |G|\Delta^2/4$ satisfies

$$
\frac{\dim C}{N} \ge 2(\rho_A + \rho_B) - 3,
$$

and, whenever $\lambda \le \delta_A\delta_B\Delta/4$, the relative distance $d(C)/N$ is at least a positive constant depending only on $\delta_A$ and $\delta_B$. In particular, for $\rho_A, \rho_B > 3/4$ and Ramanujan Cayley graphs ($\lambda \le 2\sqrt{\Delta - 1}$) with $\Delta$ large, $C$ has constant rate and constant relative distance.

## Proof sketch

The rate bound counts constraints edge by edge: each of the $|G|\Delta/2$ $A$-edges imposes $\Delta(1 - \rho_B)$ linear constraints and each of the $|G|\Delta/2$ $B$-edges imposes $\Delta(1 - \rho_A)$, at most $4N\bigl(1 - (\rho_A + \rho_B)/2\bigr)$ in total on the $N = |G|\Delta^2/4$ squares. For distance, the set $S$ of vertices seeing a nonzero local view of a low-weight codeword spans many $A$- and $B$-edges by tensor-code distance, which contradicts the square mixing lemma unless the codeword has weight $\Omega(N)$, exactly as in the Sipser-Spielman argument one dimension up.

## Depends on

- [Tensor codes on the squares of a left-right Cayley complex](square-complex-tensor-code.md)
- [Left-right Cayley complexes](left-right-cayley-complex.md)

## Proof depends on

- [Spectral expansion of the two Cayley graphs implies square-complex expansion](lr-complex-spectral.md)
- [Expander code distance](../expander-code-distance.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
