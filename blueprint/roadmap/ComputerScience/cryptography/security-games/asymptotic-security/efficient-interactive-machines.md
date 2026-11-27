# Efficient interactive machines

An interactive machine receives a positive security parameter $\lambda$, starts in its initial state and retains its state across invocations. Each invocation reads an incoming message and returns an outgoing message. Boneh–Shoup use constant-length messages; a longer word can be conveyed in several messages. The machine's running time is the **sum of its own steps over all invocations until it signals that it has halted**. It is not the time of one reply or the time spent by its environment.

The machine is efficient if there are a polynomial bound $t$ and a negligible function $\epsilon$ such that, for every $\lambda$ and every environment, even a computationally unbounded one, the probability that this total exceeds $t(\lambda)$ is at most $\epsilon(\lambda)$. The same bound and error must work for every environment. Almost-sure halting in every environment is a separate standing assumption (footnote 3); it does not follow from a negligible probability of exceeding a deadline. This is not a worst-case time bound on every random tape for a single input.

## Depends on

- [Negligible advantage](negligible-adv.md) (negligibility of the overrun probability)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §2.4.3, pp. 32–33, Definition 2.11 and footnote 3. <https://toc.cryptobook.us/>
