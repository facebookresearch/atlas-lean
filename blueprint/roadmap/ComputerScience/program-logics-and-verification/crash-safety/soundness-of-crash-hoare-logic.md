# Soundness of Crash Hoare Logic

In Crash Hoare Logic, a specification $\{P\}\ c\ \{Q\}\ \{C\}$ asserts that every execution of $c$ from a state satisfying $P$ either terminates in a state satisfying $Q$ or crashes in a state satisfying the crash condition $C$, under the crash disk model. The rules for sequencing, consequence and recovery (in particular the rule for an idempotent recovery procedure, whose crash condition implies its own precondition) are sound: every derivable specification holds for all executions with crashes, and every derivable recovery specification holds for all executions in which $c$ runs until it terminates or first crashes and, after a crash, the recovery procedure runs after reboot and may itself crash and be restarted any number of times; $c$ is never rerun.

## Depends on

- [Crash Hoare Logic](crash-hoare-logic.md)

## Sources

- H. Chen, D. Ziegler, T. Chajed, A. Chlipala, M. F. Kaashoek and N. Zeldovich, "Using Crash Hoare logic for certifying the FSCQ file system", *SOSP 2015*
