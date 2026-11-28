# Conservative extensions for linear and guarded tgds are undecidable

Whether one set of existential rules (tuple-generating dependencies) is a conservative extension of another, with respect to a data schema and a query schema, cannot be decided already for linear rules, in either the homomorphism-based or the conjunctive-query-based sense. Triviality is undecidable for guarded rules.

**Setting (Jung, Lutz and Marcinkowski).** A tuple-generating dependency (TGD) has the form $\forall \bar{x}\, \forall \bar{y}\, (\phi(\bar{x}, \bar{y}) \rightarrow \exists \bar{z}\, \psi(\bar{x}, \bar{z}))$ with conjunctions of atoms $\phi, \psi$; it is *guarded* if some body atom contains all body variables, and *linear* if its body has at most one atom. For a database $D$ (a finite set of facts over constants), $\mathrm{chase}_T(D)$ is the (possibly infinite) result of chasing $D$ with $T$, and $q_T(D)$ is the set of answers to a conjunctive query $q$ on $D$ under $T$. For finite sets of TGDs $T_1, T_2$ and schemas $\Sigma_D$ (data schema) and $\Sigma_Q$ (query schema):

- $T_2$ is *$\Sigma_D, \Sigma_Q$-hom-conservative over $T_1$* if for every $\Sigma_D$-database $D$ there is a homomorphism from $\mathrm{chase}_{T_2}(D)$ restricted to $\Sigma_Q$ into $\mathrm{chase}_{T_1}(D)$ that is the identity on the constants of $D$;
- $T_2$ is *$\Sigma_D, \Sigma_Q$-CQ-conservative over $T_1$* if $q_{T_2}(D) \subseteq q_{T_1}(D)$ for every $\Sigma_D$-database $D$ and every conjunctive query $q$ over $\Sigma_Q$;
- $T_1$ is *$\Sigma_D, \Sigma_Q$-hom-trivial* if it is $\Sigma_D, \Sigma_Q$-hom-conservative over the empty set of TGDs (*triviality*).

The decision problems take $T_1$, $T_2$ (or only $T_1$ for triviality), $\Sigma_D$ and $\Sigma_Q$ as input.

**Theorem (Jung, Lutz and Marcinkowski).** The following problems are undecidable:

1. hom-conservativity for linear TGDs;
2. CQ-conservativity for linear TGDs;
3. triviality for guarded TGDs.

Hom-conservativity implies CQ-conservativity but not conversely. The same paper shows that hom- and CQ-conservativity are decidable for frontier-one TGDs, and that triviality for linear TGDs is PSPACE-complete.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the problem whether the iteration of a given Conway function (a generalized Collatz function, specified by a modulus $\gamma$ and coefficients $\alpha_i, \beta_i$) stops, which is undecidable; the same technique was used earlier by Gogacz and Marcinkowski. The rules encode the iteration in the chase so that conservativity fails exactly when the iteration stops. Points 1 and 2 share one construction; point 3 needs a non-trivial modification of it.

## Sources

- Jean Christoph Jung, Carsten Lutz and Jerzy Marcinkowski, "Conservative Extensions for Existential Rules", Proceedings of the 19th International Conference on Principles of Knowledge Representation and Reasoning (KR 2022), pp. 195–204, 2022, <https://doi.org/10.24963/kr.2022/20>; Definition 1 (the conservativity notions), Theorem 2 (main statement), Section 4 (the reduction), Section 5 (triviality for linear TGDs) and Theorem 5 (frontier-one TGDs) of arXiv:2202.05689v1, read at <https://arxiv.org/abs/2202.05689v1>.
