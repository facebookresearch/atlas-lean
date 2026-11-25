# Box and diamond are dual in differential dynamic logic

For every hybrid program $\alpha$ and formula $P$ of differential dynamic logic, $\langle \alpha \rangle P$ and $\neg [\alpha] \neg P$ hold in
exactly the same states.

## Proof

$\langle \alpha \rangle P$ holds at $s$ iff some $\alpha$-successor of $s$ satisfies $P$, iff not every $\alpha$-successor satisfies $\neg P$, iff
$[\alpha] \neg P$ fails at $s$.

## Depends on

- [Hybrid programs and differential dynamic logic semantics](hybrid-programs-and-differential-dynamic-logic-semantics.md)

## Sources

- A. Platzer, *Logical Foundations of Cyber-Physical Systems*, Springer, 2018. Background reference.
