# Exponential edge lifting constructs the finite Bolthausen–Sznitman coalescent

Let $n\ge1$ and start from a uniform recursive tree on the singleton
partition of $[n]$. Give its edges independent rate-one exponential
ringing times, independently of the tree. At a ringing time of an edge
still present, [lift that edge and its descendant subtree](lifting-an-edge-of-a-uniform-random-recursive-tr.md).
Discard clocks of deleted edges; keep the original ringing times of
surviving edges. The block labels form a finite-state continuous-time
Markov chain $\Pi_n(t)$, initially the singleton partition.

For a state with $b\ge2$ blocks and a specified set of $k\ge2$ of them,
the rate of merging exactly those blocks is

$$\lambda_{b,k}=\frac{(k-2)!(b-k)!}{(b-1)!}.$$

There are no other off-diagonal transitions. The one-block state is
absorbing. Hence this process has the finite
[partition rate matrix](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
of the $\Lambda$-coalescent with $\Lambda$ uniform on $[0,1]$, namely the
restriction of the Bolthausen–Sznitman coalescent to $[n]$.

## Depends on

- [Finite partition-valued coalescent rate matrix](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Uniform-Lambda merger rates](merger-rate-beta-lambda-one.md)

## Proof depends on

- [Conditional uniformity and the lifting preimage count](lifting-an-edge-of-a-uniform-random-recursive-tr.md)

## Expansion

Conditionally on the full observed partition/jump-time history, the
remaining tree is uniform on its current block labels and its surviving
residual clocks are independent rate-one exponentials, independent of
that tree. This holds initially. If there are $b$ blocks, exponential
racing gives a holding time of rate $b-1$ and a uniform selected edge,
independent of the holding time. The lifting lemma preserves tree
uniformity after observing the new partition. Memorylessness preserves
the independent residual clocks; deleted clocks have no future effect.
This inductive argument justifies the Markov property relative to the
partition history, not only the next unconditional transition. The
probability of no event for a further duration $s$ is $e^{-(b-1)s}$,
independent of the tree, so the same conditional uniformity holds
between jump times as well.

For a specified $k$-block merger the lemma gives next-jump probability
$(k-2)!(b-k)!/((b-1)!(b-1))$. Multiplying by total clock rate $b-1$
gives the displayed rate. Summing over subsets checks

$$\sum_{k=2}^b\binom bk\lambda_{b,k}
 =b\sum_{k=2}^b\frac1{k(k-1)}=b-1.$$

For $n=1$ the process is constant. For $b=2$ the sole merger waits an
Exp$(1)$ time. At $b=3$ each specified pair and the triple merge have
rate $1/2$, so the total rate is $3/2+1/2=2$.
There are at most $n-1$ effective jumps. Equality of the finite generator
and initial state identifies the finite-chain law; this construction does
not need a new independent proof of the infinite coalescent's existence.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 6.1.1, Theorem 6.1, Lemma 6.1 and equations (156)–(157), after Goldschmidt–Martin (2005). The surviving-clock and full-history argument is written out above.
