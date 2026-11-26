# Protocol theories in multiset rewriting

Durgin, Lincoln, Mitchell and Scedrov model protocols by multiset rewriting over first-order *facts*. A state is a multiset of facts, including network facts
$N(t)$ for messages in transit, intruder knowledge facts $M(t)$ and role-state facts; a rule $F_1, \dots, F_k \to \exists \vec x.\ G_1, \dots, G_m$ replaces facts matching its
left side by its right side instantiated with fresh values (nonces) for $\vec x$. A *protocol theory* $T$ in restricted form consists of an initialization theory, a
role generation theory and, for each role, a sequence of rules for its steps; the *standard intruder theory* $\mathcal M$ lets the intruder read, decompose, compose,
encrypt with known keys, decrypt with known keys and send messages, and generate fresh data.

For a protocol theory $T$, a ground term $S$ (the secret) and bounds $n$, $r$ and $k$, the scenario $(T, \mathcal M, S, n, r, k)$ belongs to the set $\mathrm{PA}$ of scenarios
with an attack if some run of $T$ with the standard intruder reaches a state containing $M(S)$ in which at most $n$ protocol nonces, at most $r$ role instances and
facts of size at most $k$ appear. The secrecy problems $S_{\mathrm{size}=k}$ (given $T, \mathcal M, S$, decide whether some $n, r$ give an attack with facts of size $k$),
$S_{\mathrm{nonce}b}$ (given $T, \mathcal M, S, n, k$, decide whether some $r$ does), $S_{\mathrm{role}b}$ (given $T, \mathcal M, S, r, k$, decide whether some $n$ does) and
$S_{\mathrm{nonce}b, \mathrm{size}=k}$ are defined accordingly.

## Expansion

This node names a family of definitions. A good expansion adds a page for each of the following and links it under the dependency sections:

- Definition: facts, states and multiset rewriting with existential quantification (Section 2 of the source).
- Definition: protocol theories in restricted form, roles and the standard intruder theory (Section 3).

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Sections 2–3 (multiset rewriting, protocol theories and the intruder theory) and Section 5 (the set $\mathrm{PA}$ and the problems $S_{\mathrm{size}=k}$, $S_{\mathrm{nonce}b}$, $S_{\mathrm{role}b}$ and $S_{\mathrm{nonce}b,\mathrm{size}=k}$).
