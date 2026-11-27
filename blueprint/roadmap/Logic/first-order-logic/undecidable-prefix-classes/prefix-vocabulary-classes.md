# Prefix-vocabulary classes

A prefix-vocabulary class collects the prenex first-order sentences whose quantifier prefix matches a given pattern and whose vocabulary has at most given numbers of relation and function symbols of each arity, with or without equality. The classical decision problem asks for which classes satisfiability is decidable.

**Notation.** A prefix-vocabulary class is written

$$
[\Pi, (p_1, p_2, \dots), (f_1, f_2, \dots)] \quad \text{or} \quad [\Pi, (p_1, p_2, \dots), (f_1, f_2, \dots)]_{=}.
$$

Here $\Pi$ is a word over $\{\exists, \forall, \exists^*, \forall^*\}$ describing a set of quantifier prefixes: $\exists^*$ stands for any finite block of existential quantifiers, and $\forall^3$ abbreviates $\forall\forall\forall$. Each $p_m, f_m \leq \omega$ bounds how many relation symbols and function symbols of arity $m$ may occur, and the subscript $=$ indicates that equality may occur. The class consists of the sentences $Q_1 x_1 \cdots Q_k x_k\, \varphi$ with prefix in $\Pi$, $\varphi$ quantifier-free, and vocabulary within these bounds. The entry $\mathrm{all}$ allows any number of symbols of every arity, and $(0)$ allows none. For example, $[\exists^*\forall\exists^*, (\omega, 1), \mathrm{all}]_=$ consists of the sentences $\exists x_1 \cdots \exists x_m \forall y \exists z_1 \cdots \exists z_n\, \varphi$ with $\varphi$ quantifier-free, any number of monadic relation symbols, at most one binary relation symbol and none of higher arity, any function symbols, and equality.

A class is *decidable* if satisfiability of its sentences is decidable, and *undecidable* otherwise.

## Depends on

None.

## Proof depends on

None.

## Expansion

By Church and Turing, satisfiability of first-order sentences is undecidable, and the classification sorts every prefix-vocabulary class into decidable and undecidable ones. Among the maximal decidable classes are the Bernays–Schönfinkel class $[\exists^*\forall^*, \mathrm{all}, (0)]_=$, the Gödel class $[\exists^*\forall^2\exists^*, \mathrm{all}, (0)]$ (Gödel, Kalmár, Schütte), the monadic class $[\mathrm{all}, (\omega), (\omega)]$ (Löb; Gurevich) and $[\exists^*\forall\exists^*, \mathrm{all}, \mathrm{all}]$ (Gurevich). Rabin's class $[\mathrm{all}, (\omega), (1)]_=$ and Shelah's class $[\exists^*\forall\exists^*, \mathrm{all}, (1)]_=$ are decidable but contain infinity axioms.

## Sources

- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorems 6 and 7, which classify the classes $\Phi(\Pi, \xi, \eta)$ given by a prefix set $\Pi$ and the numbers $\xi$ of relation symbols and $\eta$ of function symbols of each arity, without equality.
- Y. Gurevich, "The decision problem for standard classes", *The Journal of Symbolic Logic* 41(2):460–464, 1976, doi:[10.2307/2272244](https://doi.org/10.2307/2272244), read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/21.pdf>: Sections 1 and 2 (standard classes with equality and function symbols, and the Main Theorem listing the decidable classes $[\exists^*, \mathrm<built-in function all>, \mathrm<built-in function all>]_=$ and $[\mathrm<built-in function all>, (\omega), (1)]_=$).
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: the slide "Prefix-vocabulary classes" (notation and example) and the slides "The complete classification: decidable cases".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
