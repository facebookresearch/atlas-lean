# Bracha's Byzantine reliable broadcast

Consider an asynchronous system of $n$ parties with authenticated point-to-point channels, one of which is the designated *leader* with an input value $v$. An adversary corrupts at most $f$ parties, with $n > 3f$, and corrupted parties may behave arbitrarily. Bracha's protocol is:
- the leader sends $\langle v\rangle$ to all parties;
- on receiving $\langle v\rangle$ from the leader, a party sends $\langle \mathrm{echo}, v\rangle$ to all, at most once;
- a party sends $\langle \mathrm{vote}, v\rangle$ to all, at most once, after receiving $\langle \mathrm{echo}, v\rangle$ from $n - f$ distinct parties or $\langle \mathrm{vote}, v\rangle$ from $f + 1$ distinct parties;
- a party delivers $v$ on receiving $\langle \mathrm{vote}, v\rangle$ from $n - f$ distinct parties.

It satisfies:
1. **Validity.** If the leader is non-faulty, every non-faulty party eventually delivers the leader's input.
2. **Agreement.** All non-faulty parties that deliver a value deliver the same value.
3. **Totality.** If some non-faulty party delivers a value, every non-faulty party eventually delivers a value.

**Proof.** No two non-faulty parties vote for different values. Consider the first such votes: each was triggered by $n - f$ echoes, and two sets of $n - f$ parties share at least $f + 1$ parties. So some non-faulty party would have echoed two different values, which the protocol forbids. If a non-faulty party delivers $v$, it saw $n - f$ votes, at least $n - 2f \ge f + 1$ of them from non-faulty parties. So every non-faulty party eventually receives $f + 1$ votes for $v$ and votes $v$ itself. All non-faulty parties then receive $n - f$ votes for $v$ and deliver $v$, which gives agreement and totality. If the leader is non-faulty, every non-faulty party echoes $v$, receives $n - f$ echoes for $v$, and votes for and delivers $v$.

The protocol sends $O(n^2)$ messages carrying $v$ and needs no cryptography beyond authenticated channels. Bracha used it to raise the resilience of asynchronous Byzantine agreement to the optimal $n > 3f$.

## Background

- [Reliable broadcast](reliable-broadcast.md): the crash-failure version of the broadcast properties

## Sources

- "Living with asynchrony: Bracha's reliable broadcast", *Decentralized Thoughts*, 19 September 2020, <https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/>: the reliable broadcast properties, the protocol, Claims 1–3 and their proofs, and the notes on message complexity and resilience.
- G. Bracha, "Asynchronous Byzantine agreement protocols", *Information and Computation* 75(2):130–143, 1987.
