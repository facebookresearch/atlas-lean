# SCPAC learnability is Σ⁰₃-complete for a computable family

There is a computable family of hypothesis classes for which the set of indices of SCPAC learnable classes is $\Sigma^0_3$-complete. So deciding SCPAC learnability is not only undecidable but sits at the third level of the arithmetical hierarchy, and $\Sigma^0_3$ is also an upper bound for every computable family.

**Setting.** Hypotheses are total computable functions $\mathbb{N} \to \{0,1\}$. A *computable family* of hypothesis classes is a sequence $(\mathcal{H}_j)_{j \in \mathbb{N}}$ of nonempty classes for which a single algorithm, given $j$, enumerates (indices of) the members of $\mathcal{H}_j$. Nonemptiness is needed for the characterizations used below: an empty class shatters no nonempty set but has no proper learner, and its set of realizable samples is empty and computable but no algorithm implements empirical risk minimization into it. The families of the hardness clauses are nonempty. Its *learnability index set* for a notion of learnability is $\{ j \in \mathbb{N} : \mathcal{H}_j \text{ is learnable} \}$.

**Theorem (Sterkenburg).**

1. For every computable family $(\mathcal{H}_j)_j$ the index set $\{ j : \mathcal{H}_j \text{ is SCPAC learnable} \}$ is in $\Sigma^0_3$.
2. There is a computable family $(\mathcal{H}_j)_j$, consisting of classes of threshold functions, for which this index set is $\Sigma^0_3$-complete.

In particular, for that family no algorithm decides SCPAC learnability of $\mathcal{H}_j$ from $j$.

## Depends on

- [SCPAC learnability](scpac-learnability.md)
- [The arithmetical class Σₙ](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [PAC learnability is Σ⁰₂-complete for a computable family](pac-learnability-is-sigma2-complete.md)

## Expansion

Upper bound: by the characterization of SCPAC learnability, $\mathcal{H}$ is SCPAC learnable if and only if its VC dimension is finite (a $\Sigma^0_2$ condition, by the upper bound for PAC learnability) and empirical risk minimization is computably implementable. The latter holds if and only if the c.e. set $B_{\mathcal{H}}$ of samples realized with zero error by some $h \in \mathcal{H}$ is computable, which is a $\Sigma^0_3$ condition on the index; the conjunction is $\Sigma^0_3$.

Hardness: let $h_i(x) = 1$ if and only if $x < i$, let $h_\omega \equiv 1$, and put $\mathcal{H}_j = \{ h_i : i \in W_j \} \cup \{ h_\omega \}$, which always contains $h_\omega$, where $(W_j)_j$ is the standard enumeration of c.e. sets. Every $\mathcal{H}_j$ has finite VC dimension, and $B_{\mathcal{H}_j}$ is computable exactly when $W_j$ is computable. Hence the learnability index set equals $\mathrm{Rec} = \{ j : W_j \text{ is computable} \}$, which is $\Sigma^0_3$-complete by a classical theorem of Rogers.

## Sources

- Tom F. Sterkenburg, "On characterizations of learnability with computable learners", Proceedings of the Thirty Fifth Conference on Learning Theory (COLT 2022), Proceedings of Machine Learning Research 178, pp. 3365–3379, 2022; Propositions 5 and 6, Lemma 2 and Theorem 2 of arXiv:2202.05041v2, <https://arxiv.org/abs/2202.05041v2>.
