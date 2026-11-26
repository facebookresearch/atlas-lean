# Two-level perfect hashing uses linear expected space

Let $S$ be a nonempty finite set of $n$ distinct keys, with a value assigned to each key.
An [indexed hash family near-universal on $S$](is-near-universal-on.md) into $m>0$ slots has a
nonempty finite index set and collision probability at most $2/m$ for every pair of distinct
keys in $S$. The ambient key type need not be finite. A uniform draw chooses an index, not a distinct function: indices that induce the same
function still count separately.

Draw a primary hash $h$ from such a family into $n$ buckets. Write $S_j$ for the
[keys assigned to bucket $j$](bucket-keys.md) and $k_j=|S_j|$. Use a
[two-level perfect hash table](../perfect-hashing/perfect-hashing.md) with
[one descriptor per primary bucket and $2k_j^2$ secondary cells per bucket](of-bucket-hashes.md).
For each nonempty bucket, suppose a finite indexed family into $2k_j^2$ slots is available,
conditional on the primary index. It need only be near-universal on $S_j$. Draw secondary indices independently, uniformly
and with replacement for that bucket until a hash is injective on $S_j$. Place the keys at
its selected slots. An empty bucket allocates no secondary cells and does not draw a hash.

**Expected space.** The average over the primary index set, taken in the rationals, satisfies

$$\mathbb E\!\left[\sum_j k_j^2\right]\le 3n-2<3n.$$

The [actual secondary allocation](../perfect-hashing/total-secondary-space.md) is
$2\sum_j k_j^2$ for every successful choice of secondary hashes, so the total allocation is
$n+2\sum_j k_j^2$ cells and has mean at most $7n-4$. The space bound does not condition on
selecting a particularly good primary hash. It does not assume independence between different
buckets' secondary choices; their outcomes don't change the allocation.

**Secondary sampling.** For a nonempty bucket of size $k$, the failure fraction $q$ is strictly
less than $1/2$, so [an injective choice exists and the expected number of draws is less than two](secondary-sampling.md).
The [probability of needing another draw after $t$ draws](secondary-attempt-tail.md) is the
rational $q^t$: it counts the length-$t$ strings consisting entirely of failing indices, divided
by the number of all length-$t$ index strings. The expected number of draws, including the first,
is the real sum of these tails for $t=0,1,\ldots$, namely $1/(1-q)$. A singleton succeeds on
its first draw. An empty bucket makes zero draws, so its tail is zero even at $t=0$.

**Lookup.** The resulting table is [valid](../perfect-hashing/valid.md). Its
[ordinary lookup](../perfect-hashing/lookup.md) returns a key's assigned value if it is in
$S$ and nothing otherwise, including when an absent query hashes to an occupied slot holding a
different key. The [lookup with a probe count](lookup-with-probes.md) returns the
[same result using at most two cell probes](lookup-with-probes-spec.md): one primary descriptor
probe, then one secondary cell probe only when the bucket is nonempty. A query into an empty
bucket returns nothing after the primary probe. This is a bound on cell probes, not a running-time
bound for computing hashes, comparing keys, constructing the tables, or copying bindings.

**Why the bounds hold.** The sum of squares counts ordered pairs of keys in a common bucket,
including the $n$ diagonal pairs. Each of the $n(n-1)$ ordered pairs of distinct keys contributes
at most $2/n$ in the uniform primary average. In a nonempty secondary bucket, the expected
number of ordered collisions between distinct keys is at most $k(k-1)\cdot 2/(2k^2)$.
Every failed draw contributes at least two ordered collisions, one in each orientation, so
$q\le (k-1)/(2k)<1/2$.

## Sources

- J. Erickson, *Algorithms*, lecture notes, Lecture 5 “Hash Tables” (Spring 2017),
  University of Illinois, <https://jeffe.cs.illinois.edu/teaching/algorithms/notes/05-hashing.pdf>,
  Sections 5.3, 5.6–5.7 and Lemma 7.
