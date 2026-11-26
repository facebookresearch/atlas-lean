# Synchronization summands contributed by one summand

Let the channel names form a type with decidable equality. Given a summand $(\alpha, P)$ and a list $t$ of summands, each a CCS action paired with a static CCS process, the synchronizations of $(\alpha, P)$ with $t$ are the list obtained from $t$ by keeping, in order, the entries $(\beta, Q)$ whose action $\beta$ is complementary to $\alpha$ (one is the input and the other the output on the same channel) and replacing each of them with $(\tau, P \mid Q)$; entries whose action is not complementary to $\alpha$ are dropped.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
