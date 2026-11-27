# Emptiness of dynamic programs is undecidable even for small fragments

A dynamic program maintains an auxiliary database under insertions and deletions of tuples, updating each auxiliary relation by a fixed formula. Whether its query relation stays empty on every modification sequence is undecidable already for first-order programs with unary input and auxiliary bits, and for quantifier-free programs with binary relations.

**Setting (Schwentick, Vortmeier and Zeume).** A *dynamic schema* is a pair $(\tau_{\mathrm{in}}, \tau_{\mathrm{aux}})$ of relational schemas. An *update program* contains, for each auxiliary relation $R$ and each modification $o \in \{\mathrm{ins}_S, \mathrm{del}_S : S \in \tau_{\mathrm{in}}\}$, an update formula $\phi^R_o(\vec{x}; \vec{y})$ over $\tau_{\mathrm{in}} \cup \tau_{\mathrm{aux}}$. A *program state* is a finite domain with an input database and an auxiliary database; applying a modification $(o, \vec{a})$ inserts or deletes $\vec{a}$ in the input and replaces each $R$ by $\{\vec{b} : \phi^R_o(\vec{a}; \vec{b}) \text{ holds in the old state}\}$. A *dynamic program* consists of an update program, a first-order definable initialization of the auxiliary relations from the (initially empty) input database, and a designated query symbol $Q \in \tau_{\mathrm{aux}}$. A $\mathrm{DynFO}$-program has first-order update formulas, a $\mathrm{DynProp}$-program quantifier-free ones; $\mathrm{DynFO}(\ell, m)$ and $\mathrm{DynProp}(\ell, m)$ restrict input relations to arity at most $\ell$ and auxiliary relations to arity at most $m$ (arity $0$ means bits). The *emptiness problem* for a class of programs asks, given a program in the class, whether $Q$ is empty in the state reached from every initially empty database by every modification sequence.

**Theorem (Schwentick, Vortmeier and Zeume).** The emptiness problem is undecidable for

1. $\mathrm{DynFO}(1, 0)$-programs (unary input relations, auxiliary bits only),
2. $\mathrm{DynProp}(1, 2)$-programs (unary input relations, binary auxiliary relations), and
3. $\mathrm{DynProp}(2, 0)$-programs (binary input relations, auxiliary bits only).

Emptiness of $\mathrm{DynFO}(2, 0)$-programs is undecidable already by the undecidability of finite satisfiability of first-order logic, whereas emptiness of $\mathrm{DynProp}(1, 1)$-programs is decidable. The paper also studies emptiness for consistent programs and history independence, which have different decidability borders.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

All three cases reduce from the emptiness problem for semi-deterministic two-counter automata, which have no input and in each state either at most one transition, or one decrementing transition and one zero test on the same counter; whether such an automaton has an accepting run is undecidable by Minsky's theorem. For every run of the automaton there is a modification sequence that lets the program simulate it, with the automaton state encoded in the program state, and the program accepts exactly when the simulated run is accepting. In case 1 the two counters are two unary input relations whose sizes are the counter values, so a zero test is an emptiness test, expressible with a quantifier. In cases 2 and 3 there are no quantifiers, so each counter is kept as a linked list of elements, maintained by quantifier-free updates, whose length gives the counter value (in case 3, the value plus one); zero is then detected without quantifiers.

## Sources

- Thomas Schwentick, Nils Vortmeier and Thomas Zeume, "Static Analysis for Logic-Based Dynamic Programs", 24th EACSL Annual Conference on Computer Science Logic (CSL 2015), LIPIcs 41, pp. 308–324, 2015, <https://doi.org/10.4230/LIPIcs.CSL.2015.308>; Section 3 (the dynamic complexity setting) and the two undecidability theorems of Section 4 ("The Emptiness Problem"), the second giving the main statement, of arXiv:1507.04537v1, read at <https://arxiv.org/abs/1507.04537v1>.
