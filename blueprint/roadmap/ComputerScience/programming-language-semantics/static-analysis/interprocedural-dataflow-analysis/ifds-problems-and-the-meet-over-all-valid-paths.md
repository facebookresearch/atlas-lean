# IFDS problems and the meet-over-all-valid-paths solution

An instance of an *interprocedural, finite, distributive, subset problem* (IFDS problem) is a tuple $(G^*, D, F, M, \sqcap)$ where
- $G^*$ is a [supergraph](supergraphs-and-valid-paths.md);
- $D$ is a finite set of dataflow facts;
- $F \subseteq 2^D \to 2^D$ is a set of distributive functions;
- $M : E^* \to F$ assigns a dataflow function to each edge;
- the meet operator $\sqcap$ is union or intersection.

The *path function* of a nonempty path $q = [e_1, \dots, e_j]$ is $\mathrm{pf}_q = f_j \circ \dots \circ f_1$ with $f_i = M(e_i)$, and that of the empty path is the identity. The *meet-over-all-valid-paths solution* assigns to each node $n$

$$\mathrm{MVP}_n = \bigsqcap_{q \in \mathrm{IVP}(s_{\mathrm{main}}, n)} \mathrm{pf}_q(\top),$$

where $\top$ is the top element of $(2^D, \sqcap)$, which is $\emptyset$ when the meet is union. Restricting the meet to valid paths, instead of all paths of the supergraph, rules out paths that return to a call site other than the one they called from. A problem with intersection as meet is handled by dualizing it to the complementary union problem: a must-be-$X$ problem becomes a may-not-be-$X$ problem. The IFDS problems include the gen/kill problems such as reaching definitions, available expressions and live variables, and non-separable problems such as truly-live variables, copy-constant propagation and possibly-uninitialized variables.

## Depends on

- [Supergraphs and valid paths](supergraphs-and-valid-paths.md)

## Sources

- T. Reps, S. Horwitz and M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", *Conference Record of the 22nd ACM Symposium on Principles of Programming Languages (POPL 1995)*, <https://research.cs.wisc.edu/wpis/papers/popl95.pdf>: Section 2, Definition 2.4 (IFDS problem instances, and the restriction to union as meet with intersection handled by complementing), Definition 2.5 (path functions) and Definition 2.6 (the meet-over-all-valid-paths solution), with the examples of IFDS problems in the abstract and the introduction.
