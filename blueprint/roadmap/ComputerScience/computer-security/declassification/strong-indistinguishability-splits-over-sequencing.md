# Strong indistinguishability splits over sequential composition

Let $\ell = (C(A), \top_I)$, with the relations of [robust declassification](robust-declassification.md) and the [typing rules for robust declassification](typing-rules-for-robust-declassification.md).

**Proposition.** If $\Gamma, pc \vdash c_1; c_2$ and $\langle M_1, c_1; c_2\rangle \cong_\ell \langle M_2, c_1; c_2\rangle$, then $\langle M_1, c_1\rangle \cong_\ell \langle M_2, c_1\rangle$, and there are memories
$N_1, N_2$ with $\langle M_1, c_1\rangle \Downarrow N_1$, $\langle M_2, c_1\rangle \Downarrow N_2$ and $\langle N_1, c_2\rangle \cong_\ell \langle N_2, c_2\rangle$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)
- [Robust declassification](robust-declassification.md)

## Proof depends on

- [Commands typed under a high program counter are invisible](commands-under-a-high-pc-are-invisible.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Proposition 7 and its proof.
