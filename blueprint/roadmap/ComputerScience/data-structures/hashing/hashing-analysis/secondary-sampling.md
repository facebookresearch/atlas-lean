# Success probability and expected draws for a secondary hash

Suppose that for a nonempty bucket of $k$ distinct keys the finite indexed family into
$2k^2$ slots is [near-universal on the keys in that bucket](is-near-universal-on.md).
There is an injective choice and the failure fraction $q$ is strictly below $1/2$. For every
$t$, the sampling tail is the fraction of length-$t$ strings of indices all of whose hashes
fail, out of all length-$t$ strings, as appropriate for independent uniform draws with replacement.
The real sum of the tails (expected number of draws, including the first) equals $1/(1-q)$ and
is strictly below $2$. For an empty bucket the expected number is zero, with no family assumption;
for a singleton it is one.
