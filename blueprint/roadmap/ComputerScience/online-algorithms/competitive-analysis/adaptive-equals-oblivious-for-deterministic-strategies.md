# Adaptive and oblivious adversaries coincide for deterministic strategies

For a deterministic online strategy, any adversary that chooses each request as a function of the strategy's current state can be replaced by the fixed request sequence it generates against that strategy: replaying the sequence obliviously induces the identical execution and the identical online cost. Hence lower bounds for deterministic strategies may be proved with adaptively generated request sequences.

## Proof sketch

By induction on the number of requests: the strategy's state after each prefix depends only on the prefix, so the generated sequence and the adaptive interaction produce the same states.

## Depends on

- [Online request-serving problem and competitive ratio](online-problem-and-competitive-ratio.md)

## Sources

- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
