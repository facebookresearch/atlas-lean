# Functional dependencies

- [Functional dependency](fd.md)
- [A functional dependency holds in a relation](holds-in.md)
- [A relation satisfies a set of dependencies](satisfies.md)
- [Entailment of functional dependencies](entails.md)
- [Derivability with Armstrong's axioms](derives.md)
- [Armstrong's axioms are sound](sound.md)
- [Decomposition rule](decompose.md)
- [Union rule](union.md)
- [Pseudotransitivity rule](pseudotrans.md)
- [Adding the left side to the right side](union-left.md)

## The attribute-closure algorithm

- [One round of the attribute-closure algorithm](closure-step.md)
- [Iterated closure rounds](closure-loop.md)
- [Attribute closure](attr-closure.md)
- [The attribute closure is a fixed point of a closure round](closure-step-attr-closure.md)
- [The attribute closure is closed under the dependencies](rhs-subset-attr-closure.md)
- [Closure witness relation](closure-witness-relation.md)
- [The closure witness satisfies the dependencies](holds-in-closure-witness-relation.md)
- [The closure algorithm decides derivability](derives-iff-subset-attr-closure.md)
- [The closure algorithm computes the attribute closure](mem-attr-closure.md)
- [Completeness of Armstrong's axioms, two-tuple form](derives-of-forall-two-tuple.md)
- [Armstrong's theorem](derives-iff-entails.md)

## Keys

- [Superkey](is-superkey.md)
- [Candidate key](is-candidate-key.md)
- [Supersets of superkeys are superkeys](mono.md)
- [Tuples that agree on a superkey are equal](eq-of-agree.md)
- [Candidate keys are the superkeys minimal under single removals](is-candidate-key-iff.md)
- [Shrinking a key along a list](shrink-key.md)
- [Key-finding algorithm](find-key.md)
- [The key-finding algorithm returns a candidate key](find-key-is-candidate-key.md)
- [Every superkey contains a candidate key](exists-is-candidate-key-subset.md)
