# Luby–Rackoff with a $\Delta$-universal first round

Let $G$ be a finite abelian group with $|G| = N$. Consider the three-round Feistel network in which round $1$ is drawn from an $\varepsilon$-almost-$\Delta$-universal hash family $h$ on $G$ and rounds $2$ and $3$ are independent uniformly random functions. For every adaptive adversary making at most $Q$ forward queries, the advantage in distinguishing this network from a uniformly random function $G^2 \to G^2$ is at most

$$
\binom{Q}{2}\left(\varepsilon + \frac{2}{N}\right),
$$

In particular three independent uniformly random round functions (for which $\varepsilon = 1/N$) give advantage $O(Q^2/N)$, recovering the Luby–Rackoff theorem. Replacing random functions by a pseudorandom function adds the PRF advantages.

## Proof sketch

The output is uniform unless two distinct queries produce the same input to round $2$ (probability at most $\varepsilon$ per pair by $\Delta$-universality) or to round $3$ (at most $1/N$ per pair, and a further $1/N$ for the output collision), which is the bad event of the difference lemma.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](../universal-hash-macs/delta-universal-hash-families.md)
- [Luby–Rackoff theorem](../pseudorandom-constructions/lubyrackoff-theorem.md)

## Proof depends on

- [The difference lemma](../../security-games/games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- Moni Naor and Omer Reingold, "On the Construction of Pseudorandom Permutations: Luby–Rackoff Revisited", Journal of Cryptology, 1999.
- Michael Luby and Charles Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing, 1988.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
