# Typing without declassification enforces noninterference

In the setting of [robust declassification](robust-declassification.md), a command $c$ satisfies *noninterference* if for every level $\ell$ and all memories $M_1 =_\ell M_2$, the configurations $\langle M_1, c\rangle$ and
$\langle M_2, c\rangle$ are weakly indistinguishable up to $\ell$.

**Theorem.** If $\Gamma, pc \vdash c$ in the [typing rules for robust declassification](typing-rules-for-robust-declassification.md) and $\mathrm{declassify}$ does not occur in $c$, then $c$ satisfies noninterference.

The proof is by induction on the evaluation of $c$, as for the Volpano–Smith–Irvine type system, using that an expression of level $\ell$ without
$\mathrm{declassify}$ evaluates equally in memories that agree up to any $\ell' \sqsupseteq \ell$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)
- [Robust declassification](robust-declassification.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 4, Definition 6 (noninterference), and Section 5, Theorem 1 with Proposition 5.
