# Markov law at a finite set of times

The canonical law at an arbitrary finite set of nonnegative times.

The generic construction does not assume `K 0 = Kernel.id`.  Consequently,
when zero is requested its marginal is `K 0 x`; callers that need a
deterministic initial value prove the identity law for their kernel.
