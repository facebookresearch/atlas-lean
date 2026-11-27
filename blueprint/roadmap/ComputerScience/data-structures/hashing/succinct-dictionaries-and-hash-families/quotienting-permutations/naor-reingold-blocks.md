# Naor–Reingold blocks for small universes

On $\{0,1\}^\ell$, a *Naor–Reingold block* is $S = h_2^{-1} \circ D_{f_t} \circ \cdots \circ D_{f_1} \circ h_1$, where $h_1, h_2$ are pairwise independent permutations, $t \ge 2$, and each $D_{f_i}$ is an unbalanced Feistel round $D_f(L, R) = (R, L \oplus f(R))$ whose round function $f_i$ is drawn from a $k$-wise $\delta'$-dependent family, all chosen independently (the $(t+2)$-round construction of Naor and Reingold). For the balanced case $\ell = 2n$, $t = 2$, the family of blocks is $k$-wise $\delta$-dependent with $\delta = k^2/2^n + k^2/2^{2n} + 2\delta'$ (Naor–Reingold, Corollary 8.1): for every $k$ distinct inputs, the output tuple is within statistical distance $\delta$ of the image under a uniformly random permutation; Corollary 8.2 gives the analogous bound for $t$ rounds. Composing $t'$ independent blocks from a $k$-wise $\delta$-dependent family gives a $k$-wise $\frac{1}{2}(2\delta)^{t'}$-dependent family (Kaplan–Naor–Reingold), so the distance decreases geometrically in $t'$ once $\delta < 1/2$. Combined with a one-round Feistel shard router $x \mapsto (x_L \oplus f(x_R), x_R)$, keys routed to the same shard have distinct suffixes $x_R$, so applying a $k$-wise $\delta$-dependent permutation to the suffixes inside each shard makes the $k$-tuples of images of keys of one shard $\delta$-close to those of a uniformly random permutation (Arbitman–Naor–Segev, Section 5.2).

## Proof sketch

Naor and Reingold show that the outer pairwise independent permutations make collisions among the inputs of the Feistel rounds unlikely, and on non-colliding inputs truly random round functions give outputs distributed as under a random permutation, which yields Theorem 3.2 (resp. 6.2); replacing the truly random round functions by $k$-wise $\delta'$-dependent ones costs at most $\delta'$ per round on $k$ inputs. Kaplan, Naor and Reingold prove the composition bound. Within one shard the router is a bijection whose second coordinate is the suffix, so distinct keys of a shard have distinct suffixes.

## Depends on

- [Universal key-quotienting permutation](../balls-to-slots-and-kick-trees/universal-key-quotienting-permutation.md)
- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)
- [Luby–Rackoff theorem](../../../../cryptography/symmetric-key/pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- M. Naor and O. Reingold, "On the Construction of Pseudorandom Permutations: Luby-Rackoff Revisited", Journal of Cryptology 12(1), 1999 (Definition 6.2, Corollaries 8.1 and 8.2).
- E. Kaplan, M. Naor and O. Reingold, "Derandomized Constructions of k-Wise (Almost) Independent Permutations", Algorithmica 55(1), 2009.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010 (Sections 5.2 and 5.3).
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.
