# Bracha's Byzantine reliable broadcast

Consider an asynchronous system of $n$ parties with authenticated point-to-point channels, one of which is the designated *leader* with an input value $v$. A fixed set $F$ of at most $f$ parties is faulty, with $n > 3f$. A faulty party may send any message to any party at any time, but only under its own name, since the channels are authenticated. Bracha's protocol is, with thresholds computed from $f$:
- the leader sends $\langle v\rangle$ to all parties;
- on receiving $\langle v\rangle$ from the leader, a party sends $\langle \mathrm{echo}, v\rangle$ to all, unless it has already sent an echo;
- a party sends $\langle \mathrm{vote}, v\rangle$ to all, unless it has already sent a vote, after receiving $\langle \mathrm{echo}, v\rangle$ from $n - f$ distinct parties or $\langle \mathrm{vote}, v\rangle$ from $f + 1$ distinct parties;
- a party delivers $v$ on receiving $\langle \mathrm{vote}, v\rangle$ from $n - f$ distinct parties, unless it has already delivered a value.

Delivering at most once is a convention that loses nothing, since by the proof below no non-faulty party receives $\langle \mathrm{vote}, \cdot\rangle$ for two different values from $n - f$ parties each. A non-faulty party applies these rules as soon as the message it has just received makes one of them apply. The protocol is a [transition system](bracha-lts.md) whose executions start from the initial state, in which nothing has been received and the leader, if it is non-faulty, has sent $\langle v\rangle$ to all parties. Each step is either a stuttering step, which changes nothing, or the receipt by a non-faulty party of a message it has not received before, sent to it by a non-faulty party or made up by a faulty one. Messages are thus received in any order and after any delay. An infinite execution is [*fair*](bracha-fair.md) when every message that a non-faulty party sends to a non-faulty party is received by it at some point; nothing constrains when, or whether, the messages of faulty parties arrive.

It satisfies:
1. **Validity.** If the leader is non-faulty, then in every fair infinite execution every non-faulty party eventually delivers the leader's input.
2. **Agreement.** In every reachable state, all non-faulty parties that have delivered a value have delivered the same value.
3. **Totality.** In every fair infinite execution, if some non-faulty party delivers a value, every non-faulty party eventually delivers a value.

**Proof.** In every reachable state, no two non-faulty parties have voted for different values. Consider the first such votes: each was triggered by $n - f$ echoes, and two sets of $n - f$ parties share at least $f + 1$ parties. So some non-faulty party would have echoed two different values, which the protocol forbids. A party that has delivered $v$ has received votes for $v$ from $n - f > f$ parties, so some non-faulty party has voted for $v$. Two values delivered by non-faulty parties therefore both have non-faulty votes, and are equal. This gives agreement, with no fairness assumption.

Totality and validity use fairness. If a non-faulty party delivers $v$ in a fair execution, it received $n - f$ votes for $v$, at least $n - 2f \ge f + 1$ of them from non-faulty parties. Every non-faulty party eventually receives these $f + 1$ votes and votes, necessarily for $v$. All non-faulty parties then receive $n - f$ votes for $v$ and deliver. If the leader is non-faulty, the non-faulty parties echo only its input $v$, so every vote, backed by $n - f > f$ echoes, is for $v$. In a fair execution every non-faulty party echoes $v$, receives $n - f$ echoes for $v$ and votes for it, then receives $n - f$ votes for $v$ and delivers $v$.

## Background

- [Reliable broadcast](reliable-broadcast.md): the crash-failure version of the broadcast properties

## Sources

- Ittai Abraham and Kartik Nayak, "Living with asynchrony: Bracha's reliable broadcast", *Decentralized Thoughts*, 19 September 2020, <https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/>: the reliable broadcast properties, the protocol, and Claims 1–3 with their proofs. This page follows their presentation of the protocol.
- G. Bracha, "Asynchronous Byzantine agreement protocols", *Information and Computation* 75(2):130–143, 1987, <https://doi.org/10.1016/0890-5401(87)90054-X>.
