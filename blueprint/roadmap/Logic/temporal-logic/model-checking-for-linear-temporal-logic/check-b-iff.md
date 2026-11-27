# Correctness of the executable LTL model checker

The model-checking procedure returns `true` on a labelled transition system with finitely many
states and actions, decidable transitions and decidable equality of states, a decidable set of
initial states, a decidable valuation and an LTL formula $\varphi$ if and only if every initial infinite run of the system
satisfies $\varphi$.
