# Completeness validation of LR(1) automata

In the setting of [soundness and safety validation of LR(1) automata](safety-validation-of-lr-1-automata.md), with grammar $G$, start symbol $S$, an LR(1) automaton and its interpreter $\mathrm{parse}(\omega, n)$:

1. **Completeness.** Suppose the completeness validator accepts the automaton and $S \xrightarrow{v} w$. Then there is $n_0$ such that, for every input stream $\omega$ and every fuel $n \ge n_0$, $\mathrm{parse}(w\omega, n)$ either is an internal error or returns the parse with semantic value $v$ and remaining input $\omega$.
2. **Unambiguity.** Suppose the token alphabet is nonempty and both the safety and the completeness validators accept the automaton. Then the grammar is semantically unambiguous: any two derivations $S \xrightarrow{v_1} w$ and $S \xrightarrow{v_2} w$ of the same word have $v_1 = v_2$.

**Proof of unambiguity.** Suppose $S \xrightarrow{v_1} w$ and $S \xrightarrow{v_2} w$. By safety the interpreter never reports an internal error. So by completeness, with enough fuel, $\mathrm{parse}(w\omega, n)$ returns both $v_1$ and $v_2$. Since $\mathrm{parse}$ is a function, $v_1 = v_2$.

Termination of the interpreter is not proved; completeness asserts acceptance only for sufficient fuel.

## Depends on

- [Soundness and safety validation of LR(1) automata](safety-validation-of-lr-1-automata.md)

## Sources

- J.-H. Jourdan, F. Pottier and X. Leroy, "Validating LR(1) parsers", *ESOP 2012*, LNCS 7211, Springer, 2012, pp. 397–416, <https://xavierleroy.org/publi/validated-parser.pdf>: Section 3.3 (Theorem 3, completeness) and Section 3.4 (Theorem 4, unambiguity, and its proof), with the remark on termination in Section 5.
