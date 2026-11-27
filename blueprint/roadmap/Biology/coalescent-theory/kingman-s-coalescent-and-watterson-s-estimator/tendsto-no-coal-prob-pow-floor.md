# Wright–Fisher coalescence times converge to exponential laws

For every natural number $k$ and every real $t \ge 0$, let $P_{\mathrm{nc}}(M, k) = \prod_{i=0}^{k-1} (1 - i/M)$. Then

$$P_{\mathrm{nc}}(M, k)^{\lfloor tM \rfloor} \to e^{-\binom{k}{2} t}$$

as the natural number $M$ tends to infinity. So after $\lfloor tM \rfloor$ Wright–Fisher generations, that is $t$ coalescent time units, the probability that $k$ lineages have not coalesced tends to $e^{-\binom{k}{2} t}$: for $k \ge 2$ this is the survival function at $t$ of the exponential distribution with rate $\binom{k}{2}$, and for $k \le 1$ there is nothing to coalesce and both sides equal $1$.
