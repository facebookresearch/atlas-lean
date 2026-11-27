# Grammar size $g$ and bidirectional macro scheme size $b$

A *straight-line program* (SLP) for $T$ is a context-free grammar with rules of the form $X \to a$ or $X \to Y Z$ that generates exactly $T$; $g(T)$ denotes the size (number of rules) of a smallest SLP for $T$. A *bidirectional macro scheme* (Storer–Szymanski) factorizes $T$ into phrases, each a single letter or a copy of another occurrence in $T$ (to the left or to the right), such that following the copy pointers from every position terminates at a letter phrase; $b(T)$ denotes the minimum number of phrases.

## Sources

- James A. Storer, Thomas G. Szymanski, "Data Compression via Textual Substitution", Journal of the ACM 29(4) (1982).
- Gonzalo Navarro, "Indexing Highly Repetitive String Collections, Part I: Repetitiveness Measures", ACM Computing Surveys 54(2) (2021), arXiv:2004.02781.
