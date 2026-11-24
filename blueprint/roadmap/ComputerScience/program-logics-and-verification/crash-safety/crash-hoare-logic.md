# Crash Hoare Logic

Crash Hoare Logic extends Hoare logic with a crash condition: a specification $\{P\}\ c\ \{Q\}\ \{C\}$ states that every execution of $c$ from a state satisfying $P$ either terminates in a state satisfying $Q$ or crashes at some point in a state satisfying $C$, over the crash disk model. A recovery specification states the postcondition of executions in which $c$ crashes any number of times, each crash followed by reboot and a run of the recovery procedure.

## Depends on

- [A crash model of disks with volatile caches](the-asynchronous-disk-model-of-crash-hoare-logic.md)

## Sources

- H. Chen, D. Ziegler, T. Chajed, A. Chlipala, M. F. Kaashoek and N. Zeldovich, "Using Crash Hoare logic for certifying the FSCQ file system", *SOSP 2015*
