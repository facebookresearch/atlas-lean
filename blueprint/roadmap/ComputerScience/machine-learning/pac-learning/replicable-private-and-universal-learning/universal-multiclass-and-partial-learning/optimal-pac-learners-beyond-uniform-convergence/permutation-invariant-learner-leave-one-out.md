# Permutation-invariant learners and leave-one-out error

A learning rule $A$ mapping finite labelled samples to hypotheses is **permutation invariant** if $A(z_{\pi(1)}, \dots, z_{\pi(n)}) = A(z_1, \dots, z_n)$ for every permutation $\pi$. Its **leave-one-out error** on a sample $S = (z_1, \dots, z_{n+1})$, $z_i = (x_i, y_i)$, is

$$
\mathrm{LOO}_A(S) = \frac{1}{n+1} \sum_{i=1}^{n+1} \mathbf{1}\big[A(S_{-i})(x_i) \ne y_i\big],
$$

where $S_{-i}$ deletes $z_i$. For i.i.d. $S \sim D^{n+1}$, $\mathbb{E}[\mathrm{LOO}_A(S)]$ equals the expected risk of $A$ trained on $n$ samples, so in-expectation bounds follow from leave-one-out bounds; turning them into high-probability bounds is the difficulty addressed below.

## Depends on

- [Expected risk](../../../../generalization-bounds-and-concentration/risk.md)

## Sources

- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167, Section 2.2 (Assumptions 2.1 and 2.3, Remark 2.2).
