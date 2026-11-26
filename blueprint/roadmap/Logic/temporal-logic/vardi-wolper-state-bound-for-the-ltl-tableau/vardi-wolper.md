# Vardi-Wolper bound

For every LTL formula $\varphi$ over a set of atoms, there is a nondeterministic Büchi automaton with a finite set of states, over the alphabet of atom valuations (sets of atoms), whose $\omega$-language is the set of words satisfying $\varphi$ and whose number of states is at most $2^{2s}$, where $s$ is the [size](../model-checking-for-linear-temporal-logic/size.md) of $\varphi$, the number of its connective and atom occurrences. This is the specialisation of the [general automaton bound](../model-checking-for-linear-temporal-logic/exists-buchi-card-le.md) to the alphabet of sets of atoms, with an atom true at a letter exactly when it belongs to that set: that result gives the same language, a finite state set and the same bound $4^{s} = 2^{2s}$. The concrete constant in the exponent belongs to an encoding with one Boolean per syntactic occurrence; the source states the bound in asymptotic form.

## Sources

- M. Y. Vardi and P. Wolper, "An automata-theoretic approach to automatic program verification", Proceedings of LICS 1986, 332-344.
