# Commands typed under a high program counter are invisible

**Proposition.** If $\Gamma, pc \vdash c$ in the [typing rules for robust declassification](typing-rules-for-robust-declassification.md) and $pc \not\sqsubseteq \ell$, then the $\ell$-projection of the trace of $\langle M, c\rangle$ is the single restricted memory
$M|_\ell$: every variable that $c$ assigns has a level above $pc$, hence not below $\ell$.

## Depends on

- [Typing rules for robust declassification](typing-rules-for-robust-declassification.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Proposition 6 and its proof.
