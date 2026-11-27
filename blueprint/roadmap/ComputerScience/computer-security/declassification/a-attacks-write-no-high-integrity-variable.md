# A-attacks write no high-integrity variable

**Proposition.** An $A$-attack, in the sense of the [typing rules for robust declassification](typing-rules-for-robust-declassification.md), contains no assignment to a high-integrity variable, that is, to a $v$ with
$\Gamma(v) \in H_I$; and it satisfies noninterference.

The typing judgement $\Gamma, (\bot_C, I(A)) \vdash a$ forces $(\bot_C, I(A)) \sqsubseteq pc \sqsubseteq \Gamma(v)$ at every assignment $v := e$ in $a$, so $I(A) \sqsubseteq I(\Gamma(v))$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)
- [Typing without declassification enforces noninterference](typing-without-declassification-enforces-noninterference.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Proposition 4 and its proof.
