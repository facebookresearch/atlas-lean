# Symbolic expressions and symbolic states

Use the arithmetic and Boolean expressions and the states of IMP, with variables indexed by natural numbers. A
*symbolic store* $\sigma$ maps each program variable to an arithmetic expression whose variables are read as the values of the
initial state; the *initial store* maps every variable $x$ to the expression $x$. For an expression $e$, its *substitution*
$\sigma(e)$ replaces every variable $x$ of $e$ by $\sigma(x)$, homomorphically through constants, sums, differences, products,
equality and order tests, negation and conjunction. The *evaluation* of $\sigma$ at an initial state $s$ is the state
$x \mapsto [\![\sigma(x)]\!]\,s$.

A *symbolic path* records a guard, a Boolean expression over the initial state; a symbolic store; and a cost, the number
of loop-body entries taken so far.

## Depends on

- [Arithmetic expressions of IMP](../../programming-language-semantics/operational-semantics-of-imp/aexp.md)
- [Boolean expressions of IMP](../../programming-language-semantics/operational-semantics-of-imp/bexp.md)
- [IMP program states](../../programming-language-semantics/operational-semantics-of-imp/state.md)

## Sources

- J. C. King, "Symbolic execution and program testing", *Communications of the ACM* 19(7):385–394, 1976 (symbolic execution, symbolic values and path conditions).
