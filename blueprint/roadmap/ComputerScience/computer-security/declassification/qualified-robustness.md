# Qualified robustness

Extend the language of [robust declassification](robust-declassification.md) with an endorsement expression $\mathrm{endorse}(e, \ell)$, which raises the integrity of the value of $e$ to $\ell$. For qualified robustness,
endorsement is given a nondeterministic semantics, $\langle M, \mathrm{endorse}(e, \ell)\rangle \to \mathit{val}$ for any value $\mathit{val}$, so a configuration has a set of traces. Two trace
sets $T_1, T_2$ are *indistinguishable up to* $\ell$ if, whenever both contain terminating traces, every terminating trace of each is $\sim_\ell$-equivalent to some
terminating trace of the other. Configurations are *weakly indistinguishable* up to $\ell$ if their trace sets are, and *strongly indistinguishable* if moreover all
their traces terminate. A context $c[\vec\bullet]$ has *qualified robustness* if it satisfies the condition of robustness with these relations in place of the
deterministic ones. The attacker's influence on endorsed values is thereby ignored.

## Depends on

- [Robust declassification](robust-declassification.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 7.1, the nondeterministic semantics of endorse, Definition 11 and Definition 12 (qualified robustness).
