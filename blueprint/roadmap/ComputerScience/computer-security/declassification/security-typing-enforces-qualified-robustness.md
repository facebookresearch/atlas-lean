# A security type system enforces qualified robustness

Extend the [typing rules for robust declassification](typing-rules-for-robust-declassification.md) with the rule for endorsement: $\Gamma, pc \vdash v := \mathrm{endorse}(e, \ell)$ if $\Gamma \vdash e : \ell'$, $\ell \sqcup pc \sqsubseteq \Gamma(v)$, $C(\ell) = C(\ell')$,
$\ell' \in L_I$ (low integrity, $I(A) \sqsubseteq I(\ell')$) and $\ell \in H_I$; attack code may not use endorsement.

**Theorem.** With this extension, if $\Gamma, pc \vdash c[\vec\bullet]$ then $c[\vec\bullet]$ satisfies [qualified robustness](qualified-robustness.md). Moreover, if $\Gamma, pc \vdash c$ and
$\mathrm{declassify}$ does not occur in $c$, then for every confidentiality level $C$ and all memories $M_1 =_{(C, \top_I)} M_2$ the configurations $\langle M_1, c\rangle$ and $\langle M_2, c\rangle$
are weakly indistinguishable up to $(C, \top_I)$ in the nondeterministic sense.

## Depends on

- [Qualified robustness](qualified-robustness.md)
- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)

## Proof depends on

- [Fair attacks are A-attacks](fair-attacks-are-a-attacks.md)
- [A-attacks write no high-integrity variable](a-attacks-write-no-high-integrity-variable.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 7.2, the typing rule for endorse, Theorem 4 and Theorem 5 with their proofs (Propositions 10–13).
