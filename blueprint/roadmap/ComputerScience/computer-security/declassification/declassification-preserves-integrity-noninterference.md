# Declassification preserves integrity noninterference

**Theorem.** If $\Gamma, pc \vdash c$ in the [typing rules for robust declassification](typing-rules-for-robust-declassification.md), declassifications included, then for every integrity level $I$ and all memories $M_1 =_{(\top_C, I)} M_2$, the
configurations $\langle M_1, c\rangle$ and $\langle M_2, c\rangle$ are weakly indistinguishable up to $(\top_C, I)$. Declassification affects only confidentiality.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)

## Proof depends on

- [Typing without declassification enforces noninterference](typing-without-declassification-enforces-noninterference.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Theorem 2 and its proof.
