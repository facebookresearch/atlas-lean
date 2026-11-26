# A security type system enforces robust declassification

Type commands with holes by judgements $\Gamma, pc \vdash c$ with the standard rules for expressions, assignment ($\ell \sqcup pc \sqsubseteq \Gamma(v)$ for $\Gamma \vdash e : \ell$),
sequencing, conditionals and loops (branches typed at $\ell \sqcup pc$ for a guard of level $\ell$) and subsumption on $pc$, together with

- *declassification:* $\Gamma, pc \vdash v := \mathrm{declassify}(e, \ell)$ if $\Gamma \vdash e : \ell'$, $\ell \sqcup pc \sqsubseteq \Gamma(v)$, $I(\ell) = I(\ell')$ and both $pc$ and $\ell'$ are
  high-integrity ($I(A) \not\sqsubseteq I(pc)$ and $I(A) \not\sqsubseteq I(\ell')$): only high-integrity data is declassified, and only at high-integrity program points;
- *holes:* $\Gamma, pc \vdash \bullet$ if $pc$ is low-confidentiality ($C(pc) \sqsubseteq C(A)$).

**Theorem.** If $\Gamma, pc \vdash c[\vec\bullet]$, then $c[\vec\bullet]$ satisfies [robustness](robust-declassification.md).

## Depends on

- [Robust declassification](robust-declassification.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Figure 4 (typing rules), the typing rule for holes and Theorem 3 with its proof.
