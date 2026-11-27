# Safety and probabilistic termination of Ben-Or's consensus under phase schedulers

In Ben-Or's binary consensus protocol with $n > 2t$ processes, quorums of size $n - t$ and crash faults, every run satisfies agreement and validity deterministically, and if at the start of a phase all processes that have not crashed hold the same estimate, every correct process decides it in that phase (the phase-by-phase form of Ben-Or's Theorem 1(ii), which is stated for the initial values). Against an adversary that fixes each phase's quorums from the state at the phase boundary before coins are flipped, the probability that not all correct processes have decided after $k + 1$ phases is at most $(1 - 2^{-n})^k$ with independent local coins and at most $2^{-k}$ with a common coin; in both cases termination occurs with probability $1$. Ben-Or proves termination with probability $1$ against a fully adaptive scheduler (Theorem 1); the phase-boundary adversary, the two geometric bounds and the common-coin variant are derived here.

## Proof sketch

Two quorums of size $n - t$ intersect, so at most one value can be proposed in stage two and a decided value locks all estimates. In a phase that starts with all live estimates equal to $v$, every stage-one quorum consists of $v$-messages only, so every process proposes $v$ and every stage-two quorum carries at least $n - t \ge t + 1$ proposals of $v$. In each phase where no proposal forces a value, all coin flips agree with the proposed value if there is one, and with each other otherwise, with probability at least $2^{-n}$ (or $1/2$ for a common coin), which makes the estimates of all live processes unanimous; independence across phases gives the geometric bound.

## Depends on

- [Ben-Or's randomized consensus](../ben-or-s-randomized-consensus.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Michael Ben-Or, "Another Advantage of Free Choice (Extended Abstract): Completely Asynchronous Agreement Protocols", Proceedings of the Second Annual ACM Symposium on Principles of Distributed Computing (PODC '83), 1983, Protocol A and Theorem 1.
