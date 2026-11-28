# Coalescence time is bounded by the maximal hitting time

**Setting.** Let $Q$ be the generator of an irreducible, reversible continuous-time Markov chain on a finite set $V$ with stationary law $\pi$ (for example simple random walk on a finite connected graph, the ancestral-lineage motion of a structured population). Place $n$ walkers at $x(1),\dots,x(n)\in V$; they move independently according to $Q$, except that walkers occupying the same site merge permanently. Let $S_t$ be the set of occupied sites, $C_k=\inf\{t:|S_t|\le k\}$ and $C=C_1$ the time until all lineages have coalesced. Write

$$T^Q_{hit}=\max_{v,w\in V}\mathbb{E}_w[H_v],\qquad T^Q_{mix}=\inf\Big\{t:\max_{x}\max_{S\subseteq V}|\mathbb{P}_x(X_t\in S)-\pi(S)|\le\tfrac14\Big\}$$

for the largest expected hitting time and the mixing time.

**Theorem.** There are universal constants $K,K_1>0$ such that for every reversible $Q$, every $n\ge1$ and every initial configuration:

1. $\mathbb{E}[C]\le K\,T^Q_{hit}$;
2. $\mathbb{E}[C_k]\le K_1\big(T^Q_{hit}/k+T^Q_{mix}\big)$ for every $k\ge1$.

Consequently the expected consensus time of the voter model on any finite graph, from any initial opinions, is at most $K\,T^{G}_{hit}$, since by duality consensus occurs exactly when the coalescing lineages traced back from all vertices have merged. This answers an open problem of Aldous and Fill. For discrete-time lazy walks, see the [hitting-time bounds on the coalescence time of coalescing lazy random walks](../coalescence-time-of-coalescing-random-walks-on-graphs/coalescence-time-bounded-by-hitting-time.md). On vertex-transitive graphs the expected meeting time of two walkers is $T_{hit}/2$, so there the full coalescence time is within a constant factor of a single pairwise meeting time, as for the Kingman coalescent on the complete graph, where $C/n\approx\sum_{i\ge1}Z_i/(i(i+1))$ with $Z_i$ i.i.d. standard exponentials.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The proof bounds coalescing walks by *walks with killings*: when two walkers meet one of them may be killed, and restricting which killings are allowed, through a time-dependent list, can only keep more walkers alive, so it gives an upper bound by coupling. It suffices to show that by a time $t_0=O(T_{mix}+T_{hit})$ at least two walkers survive with probability bounded away from $1$, uniformly in $n$ and the start; a geometric trials argument then gives $\mathbb{E}C\le KT_{hit}$. After mixing, a random quarter of the walkers are i.i.d. $\pi$-distributed, providing an abundance of good walkers in dyadic groups. Each walker in group $i$ is then killed by walkers of lower groups at successive dyadic time scales, and the probability of surviving to scale $j$ decays like $5^{j-i}$, which is summable. The $C_k$ bound follows the same scheme stopped at $k$ survivors.

## Sources

- Roberto Imbuzeiro Oliveira, "On the coalescence time of reversible random walks", *Trans. Amer. Math. Soc.* 364(4) (2012), 2109–2128. <https://doi.org/10.1090/S0002-9947-2011-05523-6>
- Preprint version (the locators in this item follow its numbering): Roberto Imbuzeiro Oliveira, "On the coalescence time of reversible random walks", arXiv:1009.0664 (2010): Section 1 (Aldous–Fill open problem, main theorem, theorem on $C_k$, voter model corollary), Section 2 (hitting and mixing times), Section 3 (coalescing walks and walks with allowed killings, domination proposition), Section 4 (reduction proposition, abundance of good walkers, survival bound, proofs of both theorems). <https://doi.org/10.48550/arXiv.1009.0664>
