# Maximal-munch lexing with rule priority

A lexer specification is an ordered list of rules $(r_1, \ell_1), \dots, (r_k, \ell_k)$ of regular expressions and token labels. A tokenization of an input $w$ is a decomposition $w = u_1 \cdots u_m$ into nonempty lexemes labelled by rules such that each $u_i$ is the longest prefix of the remaining input $u_i \cdots u_m$ that matches some rule, labelled by the first rule that matches it. When a maximal-munch tokenization of $w$ exists, it is unique.

## Sources

- D. Egolf, S. Lasser and K. Fisher, "Verbatim: a verified lexer generator", *IEEE Security and Privacy Workshops (LangSec)*, 2021
