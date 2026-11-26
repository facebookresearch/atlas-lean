# Misra–Gries step

One Misra–Gries step with parameter $k$, a natural number. The state is a summary of stored (item, counter) entries together with the number of decrement rounds so far. Processing an item $x$: if $x$ has a positive counter, or fewer than $\max(k - 1, 0)$ entries are stored, the counter of $x$ is increased by one (a new item enters with counter $1$); otherwise every stored counter is decreased by one, the entries that reach $0$ are dropped, and one round is recorded.
