# Typable contexts are robust against attacks that change low-integrity data

Let $\ell = (C(A), \top_I)$, with the relations of [robust declassification](robust-declassification.md) and the [typing rules for robust declassification](typing-rules-for-robust-declassification.md).

**Proposition.** If $\Gamma, pc \vdash c[\vec\bullet]$ and $\langle M_1, c[\vec a]\rangle \cong_\ell \langle M_2, c[\vec a]\rangle$ for an $A$-attack $\vec a$, then for every $A$-attack $\vec a'$, values
$\mathit{val}_1, \dots, \mathit{val}_n$ and variables $v_1, \dots, v_n$ of low integrity ($I(A) \sqsubseteq I(\Gamma(v_i))$), the memories $M'_j = M_j[v_1 \mapsto \mathit{val}_1, \dots, v_n \mapsto \mathit{val}_n]$
satisfy $\langle M'_1, c[\vec a']\rangle \approx_\ell \langle M'_2, c[\vec a']\rangle$. Robustness is the special case $n = 0$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)
- [Robust declassification](robust-declassification.md)

## Proof depends on

- [Typing without declassification enforces noninterference](typing-without-declassification-enforces-noninterference.md)
- [A-attacks write no high-integrity variable](a-attacks-write-no-high-integrity-variable.md)
- [Strong indistinguishability splits over sequential composition](strong-indistinguishability-splits-over-sequencing.md)
- [Attacks cannot change high-integrity results](attacks-preserve-high-integrity-data.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Proposition 9 and its proof, and the proof of Theorem 3 from it.
