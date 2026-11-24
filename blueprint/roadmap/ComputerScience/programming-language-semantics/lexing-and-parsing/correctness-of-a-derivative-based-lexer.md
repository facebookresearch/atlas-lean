# Correctness of a derivative-based lexer

Let $R$ be an ordered list of lexical rules $(\ell_1, r_1), \dots, (\ell_k, r_k)$ pairing token labels with regular expressions. The derivative-based lexer is built in three layers:
- **Matching.** A regular expression matches a string if the iterated Brzozowski derivative of the expression by the string is nullable. Checking nullability after each character yields, for a single rule, the longest prefix of the input that the rule matches.
- **First token.** $\mathrm{max\_pref}$ returns the longest prefix of the input matched by any rule, labelled by the earliest rule that matches it, together with the remaining suffix. It reports failure if no rule matches a prefix.
- **Lexing.** $\mathrm{lex}$ repeatedly takes the first token and continues on the remaining suffix. It stops, leaving the rest unprocessed, when $\mathrm{max\_pref}$ fails or returns an empty prefix. It returns a pair $(t, u)$ of a token list and an unprocessed suffix.

The specification $\mathrm{Tokens}_R(t, u)\, z$ is the maximal munch principle:
- the first token of $z$ is its maximal prefix with respect to $R$, labelled by the least-indexed matching rule;
- the remaining tokens are, inductively, those of the rest of $z$;
- the unprocessed suffix $u$ is what remains when no nonempty maximal prefix exists.

When $u$ is empty, this is a [maximal-munch tokenization](maximal-munch-lexing-with-rule-priority.md) of all of $z$.

**Theorem.** Suppose every label of $R$ is associated with exactly one regular expression.
1. **Soundness.** If $\mathrm{lex}\ R\ z = (t, u)$, then $\mathrm{Tokens}_R(t, u)\, z$.
2. **Uniqueness.** For each $z$ there is at most one pair $(t, u)$ with $\mathrm{Tokens}_R(t, u)\, z$.
3. **Completeness.** If $\mathrm{Tokens}_R(t, u)\, z$, then $\mathrm{lex}\ R\ z = (t, u)$.

Soundness is proved by strong induction on the length of $z$. Its main step shows that the label chosen by $\mathrm{max\_pref}$ is that of the earliest matching rule. Completeness follows from soundness and uniqueness, since $\mathrm{lex}$ is total. Totality is shown by well-founded recursion on the length of the remaining input. The hypothesis on labels excludes rule lists such as $[(\ell_1, a^*), (\ell_2, b^*), (\ell_1, b)]$, in which a later rule reuses the label of an earlier one.

All three properties are verified in Coq.

## Depends on

- [Maximal-munch lexing with rule priority](maximal-munch-lexing-with-rule-priority.md)

## Sources

- D. Egolf, S. Lasser and K. Fisher, "Verbatim: a verified lexer generator", *IEEE Security and Privacy Workshops (LangSec)*, 2021, <https://raw.githubusercontent.com/gangtan/LangSec-papers-and-slides/main/langsec21/papers/Egolf_LangSec21.pdf>:
    - Section II.C and Figure 4 (the maximal munch specification);
    - Section II.D (Brzozowski derivatives and nullability);
    - Section III (the matcher, max_pref, lex0 and lex);
    - Section IV (termination by accessibility);
    - Section V (soundness under rules_are_unambiguous, uniqueness, and completeness from soundness and uniqueness).
- J. A. Brzozowski, "Derivatives of regular expressions", *Journal of the ACM* 11(4):481–494, 1964.
