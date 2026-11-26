# Kleene algebra with tests subsumes propositional Hoare logic

In propositional Hoare logic a partial-correctness assertion $\{b\}\, p\, \{c\}$ relates tests $b, c$ and a program $p$; in a [Kleene algebra with tests](kleene-algebras-with-tests.md) it is encoded by the equation $b p \bar c = 0$, equivalently $bp = bpc$. Under this encoding the rules of Hoare logic become the universal Horn formulas

- composition: $bp = bpc \wedge cq = cqd \Rightarrow bpq = bpqd$;
- conditional: $bcp = bcpd \wedge \bar b c q = \bar b c q d \Rightarrow c(bp + \bar b q) = c(bp + \bar b q)d$;
- while: $bcp = bcpc \Rightarrow c(bp)^\ast \bar b = c(bp)^\ast \bar b\, \bar b c$;
- weakening: $b' \le b \wedge bp = bpc \wedge c \le c' \Rightarrow b'p = b'pc'$,

and each of them is a theorem of KAT. Hence every rule derivable in propositional Hoare logic, from premises $\{b_i\}\, p_i\, \{c_i\}$ to a conclusion $\{b\}\, p\, \{c\}$, corresponds to a theorem $b_1 p_1 \bar c_1 = 0 \wedge \dots \wedge b_n p_n \bar c_n = 0 \Rightarrow b p \bar c = 0$ of KAT. In the relational model the two encodings are the characterizations of partial correctness by [unreachability of the negated postcondition](../../kleene-algebra-with-tests/test-mul-test-compl-eq-bot-iff.md) and by [postcondition absorption](../../kleene-algebra-with-tests/test-mul-eq-test-mul-test-iff.md).

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)

## Related topics

- [Partial correctness as unreachability of the negated postcondition](../../kleene-algebra-with-tests/test-mul-test-compl-eq-bot-iff.md)
- [Postcondition absorption characterizes partial correctness](../../kleene-algebra-with-tests/test-mul-eq-test-mul-test-iff.md)

## Sources

- D. Kozen, "On Hoare logic and Kleene algebra with tests", *ACM Transactions on Computational Logic* 1(1), 2000, author copy <https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf>, Section 3, Theorem 3.1.
