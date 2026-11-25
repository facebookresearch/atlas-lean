# Howe's theorem: applicative bisimilarity is a congruence

For the untyped lambda calculus with call-by-value evaluation, use applicative similarity $\lesssim_v$ and its open extension from
[Howe's key lemma](howe-s-key-lemma.md); applicative bisimilarity $\simeq_v$ is the largest relation $B$ such that $B$ and its converse are applicative
simulations. A relation $R$ on terms in context is *compatible* if it relates each variable to itself and is preserved by abstraction and
application, a *precongruence* if it is compatible and transitive, and a *congruence* if it is moreover symmetric. The *contextual preorder*
is $\vec x \vdash e_1 \le_v e_2$ if for every context $C$ closing $e_1$ and $e_2$, $C[e_1] \Downarrow_v$ implies
$C[e_2] \Downarrow_v$; contextual equivalence $=_v$ is $\le_v \cap \ge_v$.

**Theorem.**

1. The open extension of applicative similarity is a precongruence, and the open extension of applicative bisimilarity is a congruence.
2. Applicative similarity coincides with the contextual preorder, $\vec x \vdash e_1 \lesssim_v e_2$ exactly when $\vec x \vdash e_1 \le_v e_2$, and hence applicative
   bisimilarity coincides with contextual equivalence.

Part 1 also holds for call-by-name evaluation, with applicative simulation quantifying over all closed terms instead of closed values;
this is the setting of Abramsky's lazy lambda calculus, for which Howe's method was first developed. Part 2 does not transfer in general:
for call-by-name evaluation of the untyped calculus extended with erratic choice, applicative bisimilarity is strictly contained in
contextual equivalence.

## Depends on

- [Howe's key lemma](howe-s-key-lemma.md)

## Proof depends on

- [Howe's key lemma](howe-s-key-lemma.md)

## Sources

- A. M. Pitts, "Howe's method for higher-order languages", in D. Sangiorgi and J. Rutten (eds.), *Advanced Topics in Bisimulation and Coinduction*, Cambridge University Press, 2011, Chapter 5, <https://www.cl.cam.ac.uk/~amp12/papers/howmho/howmho.pdf>: Section 5.1 (origin in Abramsky's lazy λ-calculus), Definitions 5.4.2 and 5.6.2, Theorem 5.5.5, Lemma 5.6.4, Theorem 5.6.5 and Section 5.9 (call-by-name version).
