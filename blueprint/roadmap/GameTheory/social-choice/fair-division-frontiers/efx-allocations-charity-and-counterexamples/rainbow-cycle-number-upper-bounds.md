# Upper bounds on the rainbow cycle number

For every $d \ge 1$ the rainbow cycle number satisfies $R(d) \le d^4$. Moreover $R(d) = O(d \log d)$, and this is tight up to the logarithmic factor since $R(d) \ge d$.

## Proof sketch

Assign to each vertex a random-like signature from the parts it receives arcs from and show that a long rainbow-cycle-free configuration forces a combinatorial structure (an injective selection of in-neighbours) whose size is bounded by a polynomial in $d$. The sharper $O(d \log d)$ bound follows from a probabilistic argument: sample one vertex per part uniformly at random; with positive probability the induced selection contains a rainbow cycle once $k \gg d \log d$, because each selected vertex has a selected in-neighbour in many parts.

## Depends on

- [Rainbow cycle number](rainbow-cycle-number.md)

## Proof depends on

- [Rainbow cycle number](rainbow-cycle-number.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra, "Improving EFX Guarantees through Rainbow Cycle Number", EC 2021, arXiv:2103.01628.
- H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, "EFX: A Simpler Approach and an (Almost) Optimal Guarantee via Rainbow Cycle Number", EC 2023; Operations Research (2024); arXiv:2205.07638 (titled "EFX Allocations: Simplifications and Improvements").
