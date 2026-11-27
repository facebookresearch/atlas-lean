# Well-formed parsing expression grammars are complete

Let $G$ be a [parsing expression grammar](parsing-expression-grammars.md).

- The relation $e \rightharpoonup o$, for $o \in \{0, 1, f\}$, is the least relation closed under the following rules, where $s$ ranges over $\{0, 1\}$: $\varepsilon \rightharpoonup 0$; $a \rightharpoonup 1$ and $a \rightharpoonup f$; $A \rightharpoonup o$ if $R(A) \rightharpoonup o$; $e_1 e_2 \rightharpoonup 0$ if $e_1 \rightharpoonup 0$ and $e_2 \rightharpoonup 0$; $e_1 e_2 \rightharpoonup 1$ if $e_1 \rightharpoonup 1$ and $e_2 \rightharpoonup s$, or if $e_1 \rightharpoonup s$ and $e_2 \rightharpoonup 1$; $e_1 e_2 \rightharpoonup f$ if $e_1 \rightharpoonup f$, or if $e_1 \rightharpoonup s$ and $e_2 \rightharpoonup f$; $e_1 / e_2 \rightharpoonup s$ if $e_1 \rightharpoonup s$; $e_1 / e_2 \rightharpoonup o$ if $e_1 \rightharpoonup f$ and $e_2 \rightharpoonup o$; $e^* \rightharpoonup 1$ if $e \rightharpoonup 1$; $e^* \rightharpoonup 0$ if $e \rightharpoonup f$; $!e \rightharpoonup f$ if $e \rightharpoonup s$; $!e \rightharpoonup 0$ if $e \rightharpoonup f$. It summarizes the interpretation: if $e$ succeeds on some input consuming nothing, then $e \rightharpoonup 0$; if it succeeds consuming a nonempty string, then $e \rightharpoonup 1$; if it fails, then $e \rightharpoonup f$.
- The set of *well-formed* expressions is the least set containing $\varepsilon$ and the terminals, containing $A$ if it contains $R(A)$, containing $e_1 e_2$ if it contains $e_1$ and, when $e_1 \rightharpoonup 0$, also $e_2$, containing $e_1 / e_2$ if it contains $e_1$ and $e_2$, containing $!e$ if it contains $e$, and containing $e^*$ if it contains $e$ and not $e \rightharpoonup 0$. The grammar is *well-formed* if every expression occurring in it is well-formed. Both sets are computed by iteration to a fixed point, so well-formedness is decidable; it excludes direct and mutual left recursion such as $A \leftarrow A a / a$.

**Theorem.** A well-formed grammar is complete: each of its expressions handles every input string.

**Proof sketch.** By induction on the length of the input: if all expressions of a well-formed grammar handle all strings of length at most $n$, they handle all strings of length $n + 1$, by induction on step counts, using the summary property of $\rightharpoonup$ in the cases of sequence and repetition.

## Depends on

- [Parsing expression grammars](parsing-expression-grammars.md)

## Proof depends on

- [The interpretation of a parsing expression grammar is a function](the-interpretation-of-a-parsing-expression-grammar.md)

## Sources

- B. Ford, "Parsing expression grammars: a recognition-based syntactic foundation", *Proceedings of the 31st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2004)*, <https://bford.info/pub/lang/peg.pdf>: Section 3.5 (the abstract simulation relation with its thirteen rules and the theorem that it summarizes $\Rightarrow_G$) and Section 3.6 (the inductive set of well-formed expressions, the lemma on strings of length $n + 1$, and the theorem that a well-formed grammar is complete).
