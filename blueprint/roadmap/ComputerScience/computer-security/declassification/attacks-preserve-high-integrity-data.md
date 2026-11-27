# Attacks cannot change high-integrity results

**Proposition.** Suppose $H_I \ne \emptyset$, $\Gamma, pc \vdash c[\vec\bullet]$ in the [typing rules for robust declassification](typing-rules-for-robust-declassification.md), and $\vec a$, $\vec a'$ are $A$-attacks. If $\langle M, c[\vec a]\rangle \Downarrow N$,
$\langle M', c[\vec a']\rangle \Downarrow N'$ and $M(v) = M'(v)$ for every $v$ with $\Gamma(v) \in H_I$, then $N(v) = N'(v)$ for every such $v$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)

## Proof depends on

- [A-attacks write no high-integrity variable](a-attacks-write-no-high-integrity-variable.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Proposition 8 and its proof.
