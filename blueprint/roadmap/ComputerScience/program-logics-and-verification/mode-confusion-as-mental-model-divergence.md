# Mode confusion as mental-model divergence

Let a machine model and an operator's mental model be finite automata with mode labels, [composed](user-model-and-machine-model-composition.md)
with the mental model in the role of the user model. An automation surprise is a reachable composite state that is an error, a blocking or an
augmenting state: the mode predicted by the mental model differs from the machine's actual mode, the machine can take a shared event that
the mental model does not allow, or the mental model allows a shared event that the machine cannot take. Mode confusion is the special case
of a reachable error state. Detecting either is a reachability question on the finite composite model, decided as in the
[interface correctness criterion](decidable-interface-correctness-criterion.md). These are formal predicates on models, not psychological
claims.

## Depends on

- [User model and machine model composition](user-model-and-machine-model-composition.md)

## Related topics

- [Decidable interface correctness criterion](decidable-interface-correctness-criterion.md)

## Sources

- J. Rushby, *Using model checking to help discover mode confusions and other automation surprises*, Reliability Engineering and System Safety 75(2) (2002), 167–177, Abstract and §1 (automation surprises as divergence between the behaviour of the actual system and the operator's mental model, both finite state transition systems, found by model checking). <https://www.csl.sri.com/users/rushby/papers/ress02.pdf>
- Model Checking Interactor Specifications — Campos and Harrison, ASE journal 2001 (Newcastle author page). <http://homepages.cs.ncl.ac.uk/michael.harrison/papers/camposh00.pdf> Background reference.
- Using Formal Verification to Evaluate Human-Automation Interaction: A Review — Bolton, Bass, Siminiceanu, IEEE Trans. SMC 2013. <https://drbolton.org/publications/Bolton2013SMC.pdf> Background reference.
