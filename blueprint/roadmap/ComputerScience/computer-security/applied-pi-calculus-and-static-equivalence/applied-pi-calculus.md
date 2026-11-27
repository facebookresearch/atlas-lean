# The applied pi calculus

The applied pi calculus extends the pi calculus with terms over a signature $\Sigma$ equipped with an
[equational theory](equational-theories-and-convergent-subterm-theories.md). Plain processes are built from $0$, parallel composition $P \mid Q$, replication $!P$, name
restriction $\nu n.P$, conditionals $\mathbf{if}\ M = N\ \mathbf{then}\ P\ \mathbf{else}\ Q$ (testing equality in the theory), input $N(x).P$ and output $\overline{N}\langle M\rangle.P$.
*Extended processes* $A ::= P \mid A \mid B \mid \nu n.A \mid \nu x.A \mid \{M/x\}$ add *active substitutions* $\{M/x\}$, which record messages output to the environment.
Expressions are well sorted, and only extended processes satisfying the following conditions are considered: $\mathrm{dom}(A) \cap \mathrm{dom}(B) = \emptyset$ in every $A \mid B$, where
the *domain* $\mathrm{dom}(A)$ is the set of variables $x$ that $A$ *exports*, those with an active substitution $\{M/x\}$ not under a restriction on $x$; in every $\nu x.A$
the variable $x$ has exactly one active substitution in $A$; and the substitution obtained by ignoring restrictions is cycle-free. Thus $\{M/x\} \mid \{N/x\}$ and
$\{f(y)/x\} \mid \{f(x)/y\}$ are excluded. $A$ is *closed* if $\mathrm{fv}(A) = \mathrm{dom}(A)$. The *frame* of an extended process is obtained by replacing every plain process in it
by $0$. An evaluation context is an extended process
with a hole not under input, output, conditional or replication. Structural equivalence $\equiv$ and internal reduction $\to$ (communication on a channel and the two
branches of the conditional) give the operational semantics, and a labelled semantics $A \xrightarrow{\alpha} A'$ adds input transitions $N(M)$ and output transitions that
export messages through fresh variables.

## Expansion

This node names a family of definitions. A good expansion adds a page for each of the following and links it under the dependency sections:

- Definition: syntax of terms, plain processes and extended processes, with free and bound names and variables (Section 2.1 of the source); stated in [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md).
- Definition: structural equivalence and internal reduction (Section 2.2); stated in [Structural equivalence in the applied pi calculus](structural-equivalence-in-the-applied-pi-calculus.md) and [Internal reduction in the applied pi calculus](internal-reduction-in-the-applied-pi-calculus.md).
- Definition: labelled operational semantics (Section 4.3); stated in [Labelled transitions in the applied pi calculus](labelled-transitions-in-the-applied-pi-calculus.md).

## Depends on

- [Equational theories and convergent subterm theories](equational-theories-and-convergent-subterm-theories.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 2 (syntax, informal semantics and operational semantics) and Section 4.3 (labelled operational semantics).
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Chapter 5 (the calculus and its formal semantics).
