# Interval evaluation of an arithmetic expression

Let $e$ be an arithmetic expression built from variables $x_1, \dots, x_n$, each of which may occur several times, by the binary operations $+$, $-$, $\times$ and $\div$; let $f$ be the real function it computes, defined where no divisor vanishes. For [intervals](interval.md) $I_1, \dots, I_n$, the *interval evaluation* $E(I_1, \dots, I_n)$ of $e$ is defined by recursion on $e$: a variable $x_i$ evaluates to $I_i$, and $e_1 \circ e_2$ evaluates to $E_1 \circ E_2$ by the [interval arithmetic operations](interval-arithmetic-operations.md), where $E_1$ and $E_2$ are the evaluations of $e_1$ and $e_2$. The evaluation is *defined* when every divisor interval met in the recursion excludes $0$. As a function of $(I_1, \dots, I_n)$ it is the *natural interval extension* of $e$; it depends on the expression, not only on $f$.

## Depends on

- [Interval arithmetic operations](interval-arithmetic-operations.md)
- [Interval](interval.md)

## Sources

- T. Hickey, Q. Ju and M. H. van Emden, "Interval arithmetic: from principles to implementation", *Journal of the ACM* 48(5):1038–1068, 2001, Section 3, the evaluation $E|V$ of an expression $E$ in an environment $V$ that assigns values to its variables and functions to its function symbols, with intervals for the variables and the interval operations for the function symbols. <https://doi.org/10.1145/502102.502106>
