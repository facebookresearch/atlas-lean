# Operations on an atomic register

An operation of one thread on a single atomic register holding a natural number is one of:

- $\mathrm{write}(v)$ for $v \in \mathbb{N}$, which stores $v$;
- $\mathrm{read}$, which observes the register and does not change its value.

An execution is an interleaving: a list of thread-tagged operations $(t, o)$ with thread identifier $t \in \mathbb{N}$.
