---
article_id: af_27f992221a2362843592ae2e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.crochemore_squarefree_test_set
---

# Crochemore Squarefree Criterion

Crochemore's finite test: a letter map `f` on the ternary alphabet induces a
squarefreeness-preserving free-monoid morphism (via `List.flatMap`) on all words
if and only if it does so on squarefree words of length at most 5.

Currie lines 99-100 state that a morphism `f` defined on `Σ*` preserves
squarefreeness exactly when it preserves squarefreeness on words of length at
most 5 (authoritative source
`https://cs.uwaterloo.ca/journals/JIS/VOL22/Currie/currie20.tex`,
span SHA-256
`ae0ba8107ccc5dfcd1a4065609be8a31f1a809ea3f1f9b37ce7a2cd762dd5bf9`);
the primary reference is Crochemore, Theoret. Comput. Sci. 18(2) (1982),
DOI 10.1016/0304-3975(82)90023-8. The source states no non-erasing hypothesis
for this criterion, so none is formalized.

Proof: reduce erasing morphisms first, then apply Currie's synchronization
method to a shortest square occurrence and its shortest source-word cover.

## Depends on

- [Is Square Free Word](square-free-word/is-square-free-word.md)
- [Ternary Alphabet](square-free-word/ternary-alphabet.md)

## Proof depends on

- [Of is Infix](square-free-word/of-is-infix.md)
- [Is Word Square](square-free-word/is-word-square.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion](../../../../../sources/v2/MathlibExt.md)
