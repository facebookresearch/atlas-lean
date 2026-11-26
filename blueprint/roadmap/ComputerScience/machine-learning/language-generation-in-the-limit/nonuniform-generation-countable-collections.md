# Every countable collection is non-uniformly generatable but not with membership queries alone

Every countable collection of infinite languages is non-uniformly generatable: there is a generator such that for each target $K$ there is $d^*(K)$, depending only on $K$, after which every output is valid as soon as $d^*(K)$ distinct strings of $K$ have been seen. However, no algorithm that accesses the languages only through membership queries can non-uniformly generate even for some collections consisting of just two languages. Uniform generation with feedback (the generator may ask whether a string belongs to the target) is characterized exactly by the finiteness of a complexity measure of the collection.

## Proof sketch

Order the collection; for the target $L_z$, the finitely many earlier languages that do not contain $K$ are each refuted by some element of $K$, and the number of distinct elements needed for these refutations defines $d^*(K)$; a generator that, after seeing distinct strings, outputs from the intersection of all consistent languages among the first few indices, with the number of indices growing with the count of distinct strings, is valid once the count passes $d^*(K)$. The membership-query lower bound constructs two languages whose relevant intersection cannot be certified by finitely many membership queries.

## Depends on

- [The closure dimension characterizes uniform generatability](closure-dimension-characterizes-uniform-generation.md)
- [Every countable collection of languages is generatable in the limit](kleinberg-mullainathan-generation-theorem.md)

## Proof depends on

- [The closure dimension characterizes uniform generatability](closure-dimension-characterizes-uniform-generation.md)
- [Every countable collection of languages is generatable in the limit](kleinberg-mullainathan-generation-theorem.md)

## Sources

- M. Charikar, C. Pabbaraju, "Exploring Facets of Language Generation in the Limit", COLT (2025), arXiv:2411.15364.
- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
