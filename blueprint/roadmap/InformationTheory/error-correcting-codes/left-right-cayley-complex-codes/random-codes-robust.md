# Random pairs of codes are two-sided robustly testable

For all $\rho_a, \rho_b \in (0, 1)$ there are $\delta_1, \delta_2 > 0$ such that the following holds. Let $C_A, C_B \subseteq \mathbb{F}_2^{\Delta}$ be independent uniformly random linear codes of dimensions $\rho_a \Delta$ and $\rho_b \Delta$. Then, with probability tending to $1$ as $\Delta \to \infty$, the four codes $C_A, C_B, C_A^{\perp}, C_B^{\perp}$ have minimum distance at least $\delta_1 \Delta$, and both $C_A \otimes C_B$ and the tensor product of the duals $C_A^{\perp} \otimes C_B^{\perp}$ are $\delta_2$-agreement testable. Equivalently, both pairs $(C_A, C_B)$ and $(C_A^{\perp}, C_B^{\perp})$ are $\delta_2 \Delta$-robust: every $c \in C_A \otimes \mathbb{F}_2^{\Delta} + \mathbb{F}_2^{\Delta} \otimes C_B$ splits as $c = c_a + c_b$ with $c_a \in C_A \otimes \mathbb{F}_2^{\Delta}$, $c_b \in \mathbb{F}_2^{\Delta} \otimes C_B$ and $|c| \ge \delta_2 \Delta \,(\#\text{nonzero columns of } c_a + \#\text{nonzero rows of } c_b)$.

## Proof sketch

For one pair this is Theorem 2.10 of Dinur, Hsieh, Lin and Vidick, with explicit admissible $\delta_1, \delta_2$: a counting argument in the style of the Gilbert-Varshamov bound declares certain low-weight words bad and shows by a union bound that with high probability no bad word is a codeword, organizing the words by rank. The dual of a uniformly random code of dimension $\rho \Delta$ is a uniformly random code of dimension $(1-\rho)\Delta$, so the same theorem applies to $(C_A^{\perp}, C_B^{\perp})$, and a union bound gives both conclusions at once (Corollary 2.11). Robustness and agreement testability coincide in this normalization because the associated chain complex is exact (Definitions 2.8 and 2.9).

## Depends on

- [Agreement testability and robustness of tensor codes](agreement-testability-tensor.md)

## Sources

- I. Dinur, M.-H. Hsieh, T.-C. Lin, T. Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023), arXiv:2206.07750, Theorem 2.10 and Corollary 2.11.
