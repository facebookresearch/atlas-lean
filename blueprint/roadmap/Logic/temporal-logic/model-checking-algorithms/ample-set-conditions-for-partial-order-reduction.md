# Ample-set conditions for partial-order reduction

Let $TS$ be a finite transition system without terminal states whose transitions are labelled by actions, each action enabled in a state $s$ leading to a unique successor. Two actions $\alpha \ne \beta$ are *independent* if whenever both are enabled in $s$, executing either keeps the other enabled and executing them in either order leads to the same state. A function assigning to each state $s$ a set $\mathrm{ample}(s) \subseteq \mathrm{Act}(s)$ of enabled actions satisfies the ample-set conditions if

- (A1) $\mathrm{ample}(s) \ne \emptyset$;
- (A2) for every finite execution $s \xrightarrow{\beta_1} s_1 \cdots \xrightarrow{\beta_n} s_n \xrightarrow{\alpha} t$ of $TS$ in which $\alpha \notin \mathrm{ample}(s)$ depends on some action of $\mathrm{ample}(s)$, some $\beta_i$ belongs to $\mathrm{ample}(s)$;
- (A3) if $\mathrm{ample}(s) \ne \mathrm{Act}(s)$ then every action of $\mathrm{ample}(s)$ is a stutter action (it does not change the atomic propositions);
- (A4) for every cycle $s_0 s_1 \cdots s_n = s_0$ of the reduced system and every action $\alpha$ enabled in some state $s_i$ of the cycle, $\alpha \in \mathrm{ample}(s_j)$ for some state $s_j$ of the cycle.

Conditions (A1)–(A3) are imposed on the states of the reduced system and (A4) on its cycles. The stronger requirement that every cycle of the reduced system contain a state $s$ with $\mathrm{ample}(s) = \mathrm{Act}(s)$ implies (A4) in the presence of (A2) and is a common sufficient variant.

The reduced system explores from each state only the transitions of its ample set.

## Expansion

This page becomes ready once these prerequisites are stated:

- Action-deterministic labelled transition system with atomic propositions (statement prerequisite)

## Sources

- C. Baier and J.-P. Katoen, *Principles of Model Checking*, MIT Press, 2008
- J.-P. Katoen, *Model Checking*, Lecture 17: Partial-order reduction, RWTH Aachen University, 2019, slides 31–36, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec17.pdf>
