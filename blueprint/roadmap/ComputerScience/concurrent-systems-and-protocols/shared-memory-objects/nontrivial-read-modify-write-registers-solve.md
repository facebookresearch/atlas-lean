# Nontrivial read-modify-write registers solve two-process consensus

Let a register support a read-modify-write operation that atomically replaces its value $v$ by $f(v)$ and returns $v$, where $f$ is not the identity. Then such registers, together with atomic registers, solve wait-free consensus for two processes: each process announces its input and applies the operation once to a register initialized to a value $v_0$ with $f(v_0) \ne v_0$; the process that sees $v_0$ decides its own input, and the other decides the announced input of the first. Hence every nontrivial read-modify-write register has consensus number at least $2$.

## Depends on

- [Consensus number](consensus-number.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Theorem 3
