# Dinur–Evra–Livne–Lubotzky–Mozes: explicit c3-LTCs from left-right Cayley complexes

There exist constants $r, \delta, \kappa > 0$, $q \in \mathbb{N}$ and an explicit family of left-right Cayley complexes $X_n = \mathrm{Cay}^2(A_n, G_n, B_n)$ with $G_n = \mathrm{PSL}_2(\mathbb{F}_{q_n})$ for a growing sequence of prime powers $q_n$ and $|A_n| = |B_n| = \Delta$ fixed, together with fixed base codes $C_A, C_B \subseteq \mathbb{F}_2^{\Delta}$, such that the codes $C[G_n, A_n, B_n, C_A, C_B]$ form a $c^3$-LTC family with rate at least $r$, relative distance at least $\delta$, locality $q = \Delta^2$ and soundness $\kappa$.

## Proof sketch

Take $A_n, B_n$ such that both Cayley graphs are Ramanujan (Lubotzky-Phillips-Sarnak/Morgenstern type), so $\lambda \le 2\sqrt{\Delta - 1}$. Choose $C_A, C_B$ random of rate above $3/4$, which are agreement testable with constant parameters for large $\Delta$; the condition $\lambda \le c_0\delta^2\kappa\Delta$ then holds for $\Delta$ large. Rate and distance follow from the counting and mixing argument and local testability from the soundness of the vertex tester.

## Depends on

- [c3-locally testable code families](c3-ltc-family.md)
- [Left-right Cayley complexes](left-right-cayley-complex.md)
- [Tensor codes on the squares of a left-right Cayley complex](square-complex-tensor-code.md)

## Proof depends on

- [Soundness of the vertex tester for left-right Cayley complex codes](dellm-soundness.md)
- [Rate and distance of left-right Cayley complex codes](lr-code-rate-distance.md)
- [Random pairs of codes are two-sided robustly testable](random-codes-robust.md)
- [Good locally testable codes of every rate below one](../locally-testable-codes/theorem-1-2.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
