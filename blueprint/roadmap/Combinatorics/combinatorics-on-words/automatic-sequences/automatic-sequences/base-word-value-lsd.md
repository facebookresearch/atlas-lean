# Value of a base-$k$ digit word, least significant digit first

For a natural number $k$,
the value of a finite word $d_0 d_1 \cdots d_{m-1}$ of digits $d_i \in \{0, 1, \dots, k-1\}$ is
the natural number $\sum_{i < m} d_i k^i$, so the first digit is the least significant one; the
empty word has value $0$.

## Sources

- Zoran Šunić, *Rational Tree Morphisms and Transducer Integer Sequences: Definition and Examples*, Journal of Integer Sequences 10 (2007), Article 07.4.3, Section 3, remark after Definition 3.1 (automata read integer representations starting from the least significant digit and tolerate trailing zeros), https://cs.uwaterloo.ca/journals/JIS/VOL10/Sunic/cubefree.html
