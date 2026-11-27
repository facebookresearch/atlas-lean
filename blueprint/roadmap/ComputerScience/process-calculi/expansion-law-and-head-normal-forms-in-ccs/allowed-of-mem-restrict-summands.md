# Every entry of a restricted list of summands has a permitted action

Let the channel names form a type with decidable equality. Let $L$ be a finite list of channel names and $s$ a list of summands, each a CCS action paired with a static CCS process. Every entry $(\alpha, R)$ of the list obtained by restricting $s$ by $L$ (keeping the entries with an action permitted by $L$, each continuation put under $\setminus L$) has an action $\alpha$ permitted by $L$: $\alpha$ is $\tau$, or an input or output on a channel not in $L$.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.
