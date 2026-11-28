# Soundness and safety validation of LR(1) automata

Fix a context-free grammar $G$ with start symbol $S$, whose productions carry semantic actions, and write $S \xrightarrow{v} w$ when $S$ derives the token word $w$ with semantic value $v$. Fix an LR(1) automaton for $G$, produced by an untrusted generator. Each state $\sigma$ carries its incoming symbol $\mathrm{incoming}(\sigma)$ and two annotations: $\mathrm{pastSymbols}(\sigma)$, a word of symbols, and $\mathrm{pastStates}(\sigma)$, a sequence of sets of states. These describe the part of the stack nearest the top. The automaton drives a pushdown interpreter $\mathrm{parse}(\omega, n)$ on an input stream $\omega$ with fuel $n$. The interpreter returns a parse, a syntax error, fuel exhaustion, or an internal error when the stack does not have the expected shape.

1. **Soundness.** For every automaton, if $\mathrm{parse}(\omega, n)$ returns a parse with semantic value $v$ and remaining input $\omega'$, then $\omega = w\omega'$ for a word $w$ with $S \xrightarrow{v} w$. The invariant is that the symbols of the states on the stack derive the consumed input.
2. **Safety.** Suppose the safety validator accepts the automaton. Then $\mathrm{parse}(\omega, n)$ is never an internal error, for every input stream $\omega$ and every fuel $n$. The validator checks the following decidable conditions:
    - for every transition from $\sigma$ to $\sigma'$, $\mathrm{pastSymbols}(\sigma')$ is a suffix of $\mathrm{pastSymbols}(\sigma)\,\mathrm{incoming}(\sigma)$ and $\mathrm{pastStates}(\sigma')$ is a suffix of $\mathrm{pastStates}(\sigma)\{\sigma\}$;
    - for every reduction by $A \to \alpha$ in state $\sigma$, $\alpha$ is a suffix of $\mathrm{pastSymbols}(\sigma)\,\mathrm{incoming}(\sigma)$, and the goto table is defined on $A$ at every state that can lie $|\alpha|$ cells down the stack;
    - every accepting state differs from the initial state, has incoming symbol $S$, and has $\{\mathrm{init}\}$ as its past states.

The safety conditions ignore lookahead: an LR(1) automaton is safe exactly when its underlying nondeterministic LR(0) automaton is. So the validator does not depend on how the automaton was constructed.

## Sources

- J.-H. Jourdan, F. Pottier and X. Leroy, "Validating LR(1) parsers", *ESOP 2012*, LNCS 7211, Springer, 2012, pp. 397–416, <https://xavierleroy.org/publi/validated-parser.pdf>: Section 3.1 (Theorem 1, soundness) and Section 3.2 (Theorem 2, safety, and the conditions checked by the safety validator).
