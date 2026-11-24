# First-order arithmetic is expressive for while programs

Use the assertion language $\mathcal{N}$ with its standard interpretation in $\mathbb{Z}$ from
[first-order arithmetic as an assertion language](first-order-arithmetic-as-an-assertion-language.md), and while programs whose
expressions are terms and quantifier-free formulas of $\mathcal{N}$. For an assertion $P$ and a program $A$, let $x_1, \dots, x_n$ list the
variables free in $P$ or occurring in $A$. The *post relation* of $P$ and $A$ holds of $(d_1, \dots, d_n)$ exactly when some initial state
satisfying $P$ leads to a terminating execution of $A$ whose final values of $x_1, \dots, x_n$ are $d_1, \dots, d_n$. The assertion language
is *expressive* if for every assertion $P$ and program $A$ some formula of the language with free variables $x_1, \dots, x_n$ defines
the post relation of $P$ and $A$ in the interpretation.

**Theorem.** $\mathcal{N}$ is expressive for while programs under its standard interpretation in $\mathbb{Z}$.

The post relation is the graph of a partial recursive function of the initial values, restricted to initial values
satisfying $P$, and every partial recursive function is definable in $\mathcal{N}$. The fragment without multiplication is not
expressive: every recursively enumerable set is the post relation of $0 = 0$ and some program, while truth in that
fragment is decidable by Presburger's theorem.

## Depends on

- [First-order arithmetic as an assertion language](first-order-arithmetic-as-an-assertion-language.md)

## Expansion

State the definability of the partial recursive functions computed by while programs in $\mathcal{N}$, for example by coding
finite sequences of states with Gödel's $\beta$ function.

## Sources

- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 6 (definition of the post relation and of expressiveness, Lemma 5, and the remark on the language without multiplication).
