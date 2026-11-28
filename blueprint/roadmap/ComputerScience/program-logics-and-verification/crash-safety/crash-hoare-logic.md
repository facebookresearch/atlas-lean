# Crash Hoare Logic

Crash Hoare Logic extends Hoare logic with a crash condition: a specification $\{P\}\ c\ \{Q\}\ \{C\}$ states that every execution of $c$ from a state satisfying $P$ either terminates in a state satisfying $Q$ or crashes at some point in a state satisfying $C$, over the crash disk model. A recovery specification for $c$ with recovery procedure $r$ states the postcondition of executions in which $c$ runs until it terminates or first crashes; after a crash the machine reboots and runs $r$, and only $r$ may then crash and be restarted after reboot, any number of times, until it terminates. The main command $c$ is never rerun.

## Depends on

- [A crash model of disks with volatile caches](the-asynchronous-disk-model-of-crash-hoare-logic.md)

## Sources

- H. Chen, D. Ziegler, T. Chajed, A. Chlipala, M. F. Kaashoek and N. Zeldovich, "Using Crash Hoare logic for certifying the FSCQ file system", *SOSP 2015*
