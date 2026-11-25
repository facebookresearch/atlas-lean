# Model checking for linear temporal logic

- [Truth-annotation states of the LTL tableau](state.md)
- [Root truth bit of a tableau annotation](value.md)
- [Number of until fairness obligations](obligation-count.md)
- [Local transition relation of the LTL tableau](step.md)
- [Boolean test for an until fairness obligation](obligation.md)
- [Fairness of a tableau annotation sequence](fair.md)
- [Generalized Büchi tableau for an LTL formula](automaton.md)
- [Tableau fairness is generalized Büchi acceptance](fair-iff.md)
- [Tableau acceptance via initial, local and fairness conditions](mem-language-iff.md)
- [LTL tableau accepts exactly the satisfying words](mem-automaton-iff.md)
- [Generalized LTL tableau language equals the formula language](language-automaton.md)
- [Büchi automaton for an LTL formula](buchi.md)
- [Büchi automaton language equals the LTL formula language](language-buchi.md)
- [Büchi automaton accepts exactly the satisfying words](mem-buchi-iff.md)
- [Every LTL formula has a finite-state Büchi automaton](exists-buchi.md)
- [Initial infinite run of a transition system](is-run.md)
- [Runs are sequences with a transition between adjacent states](is-run-iff.md)
- [Product of a transition system with a Büchi recognizer](product.md)
- [Product accepts exactly the runs accepted by the recognizer](mem-product-iff.md)
- [Counterexample product for an LTL formula](counterexample.md)
- [Satisfaction of an LTL formula by all initial runs](models.md)
- [Counterexample words are runs violating the formula](mem-counterexample-iff.md)
- [Finite-model LTL satisfaction iff no counterexample lasso](models-iff-no-lasso.md)
- [LTL satisfaction iff the counterexample language is empty](models-iff-language-empty.md)
- [Computable fairness-counter update](advance.md)
- [Computable counter update equals generic degeneralization](next-count-eq-advance.md)
- [Büchi transition test via the computable counter update](buchi-tr-iff.md)
- [Executable full-LTL model checker](check-b.md)
- [Correctness of the executable LTL model checker](check-b-iff.md)

## Size of the Büchi automaton

- [Size of an LTL formula](size.md)
- [Formulas have positive size](one-le-size.md)
- [Exact state count of the LTL tableau](nat-card-state.md)
- [Fairness obligations are fewer than the formula size](obligation-count-lt-size.md)
- [Exponential state bound for the Büchi automaton of an LTL formula](nat-card-buchi-state-le.md)
- [Vardi–Wolper translation with an exponential state bound](exists-buchi-card-le.md)

## Model checking as language inclusion

- [Büchi automaton of a transition system](system-automaton.md)
- [The language of the system automaton is the set of runs](mem-system-automaton-iff.md)
- [LTL model checking is language inclusion](models-iff-language-le.md)
- [LTL model checking is emptiness of an intersection](models-iff-inf-language-neg-eq-bot.md)

## Satisfiability and validity

- [Satisfiable LTL formula](satisfiable.md)
- [Valid LTL formula](valid.md)
- [Validity is unsatisfiability of the negation](valid-iff-not-satisfiable-not.md)
- [LTL satisfiability is Büchi nonemptiness](satisfiable-iff-language-ne-bot.md)
- [LTL satisfiability by the lasso criterion](satisfiable-iff-has-lasso.md)
- [Executable LTL satisfiability test](sat-b.md)
- [Correctness of the executable satisfiability test](sat-b-iff.md)

## Related topics

- [Labelled transition systems](../../../ComputerScience/process-calculi/labelled-transition-systems/README.md): the models checked here are labelled transition systems, the same objects that give process calculi their operational semantics.
- [Program logics and verification](../../../ComputerScience/program-logics-and-verification/README.md): deductive verification of programs, the proof-based counterpart of algorithmic model checking of finite-state systems.
- [Concurrent systems and protocols](../../../ComputerScience/concurrent-systems-and-protocols/README.md): finite-state protocols such as the alternating-bit protocol, the typical inputs of LTL model checking.
