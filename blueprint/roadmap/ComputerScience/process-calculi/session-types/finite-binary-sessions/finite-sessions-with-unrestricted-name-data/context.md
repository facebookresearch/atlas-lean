# Per-channel session context of a thread

A session context is a function $\Gamma : \mathbb{N} \to \mathcal{S}$ from channel numbers to finite
binary session types: $\Gamma(a)$ is the remaining protocol of the thread on the free channel
constant numbered $a$. It is total, so a channel not in use is given $\mathrm{end}$.
