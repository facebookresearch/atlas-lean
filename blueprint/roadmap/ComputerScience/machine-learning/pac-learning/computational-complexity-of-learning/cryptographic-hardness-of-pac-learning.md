# Cryptographic hardness of (improper) PAC learning

Conditional theorem. Suppose there is a family of pseudorandom functions whose members are computed by
polynomial-size circuits in a class $C$ and that is secure against every probabilistic polynomial-time
distinguisher with oracle (membership-query) access. Then $C$ is not efficiently PAC learnable, even
improperly and even under the uniform distribution with membership queries, by any learner whose output
hypotheses can be evaluated in polynomial time. In particular, polynomial-size circuits are not efficiently
learnable under this assumption. The assumption is not proved; efficient evaluation of the output hypothesis
is needed for the distinguisher in the reduction.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Security game (attack experiment) and advantage.

## Depends on

- [Efficient PAC learning of representation classes](efficient-pac-learning-of-representation-classes.md)

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27(11) (1984) 1134–1142, closing discussion: an encryption scheme immune to chosen-plaintext attack yields easy-to-compute functions that are not learnable, with reference to the pseudorandom functions of Goldreich, Goldwasser and Micali. <http://web.mit.edu/6.435/www/Valiant84.pdf>
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Section 8.4 (hardness of learning from cryptographic assumptions, with a trapdoor-function argument and a pointer to Kearns and Vazirani, Chapter 6). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>

The reduction: a learner with polynomial-time evaluable output, run with the oracle, yields a hypothesis that agrees with a pseudorandom function on a fresh uniform point with probability at least $1 - \varepsilon$, but with a truly random function only with probability about $1/2$; this distinguishes the two.
