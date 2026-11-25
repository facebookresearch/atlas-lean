# Adding a natural number to a dyadic integer

Let $\omega$ be a dyadic integer, written as
its sequence $(\omega_0, \omega_1, \dots)$ of binary digits $\omega_i \in \{0, 1\}$ (least
significant digit first), and let $j$ be a natural number with binary digits $j_0, j_1, \dots$.
The dyadic integer $\omega + j$ has $i$-th digit $(\omega_i + j_i + c_i) \bmod 2$, where the
carries are given by $c_0 = 0$ and $c_{i+1} = \lfloor (\omega_i + j_i + c_i)/2 \rfloor$.

## Sources

- Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 5 (dyadic integers and the odometer).
