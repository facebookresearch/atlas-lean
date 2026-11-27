# Terms and processes of the applied pi calculus

Fix a *signature* $\Sigma$, a finite set of function symbols $f$, each with an arity $l$ (constants have arity $0$) and a sort $f : \tau_1 \times \dots \times \tau_l \to \tau$, a set of *names* $a, b, c, \dots, k, n, s$
and a set of *variables* $x, y, z$, each name and variable having a sort (among them a sort $\mathrm{Channel}$), with infinitely many names and infinitely many variables of
each sort. *Terms* $M, N$ are names, variables
and applications $f(M_1, \dots, M_l)$ with $l$ the arity of $f$, well sorted: each $M_j$ has sort $\tau_j$ and the application has sort $\tau$; a term is *ground* if it has no variables. *Plain processes* are

$$P, Q ::= 0 \mid P \mid Q \mid\ !P \mid \nu n.P \mid \mathbf{if}\ M = N\ \mathbf{then}\ P\ \mathbf{else}\ Q \mid N(x).P \mid \overline{N}\langle M\rangle.P,$$

the null process, parallel composition, replication, name restriction, a conditional on equality in the equational theory, input of $x$ on the channel $N$
and output of $M$ on $N$. *Extended processes* add variable restriction and *active substitutions* $\{M/x\}$:

$$A, B ::= P \mid A \mid B \mid \nu n.A \mid \nu x.A \mid \{M/x\}.$$

All expressions are well sorted: in $N(x).P$ and $\overline{N}\langle M\rangle.P$ the subject $N$ has sort $\mathrm{Channel}$ (and $M$ any sort), in
$\mathbf{if}\ M = N\ \mathbf{then}\ P\ \mathbf{else}\ Q$ the terms $M$ and $N$ have the same sort, and an active substitution $\{M/x\}$ has $M$ of the sort of $x$; substitutions
preserve sorts. Names are bound by $\nu n$ and variables by $\nu x$ and by input; $\mathrm{fn}(A)$ and $\mathrm{fv}(A)$ are the free names and variables, and the *domain*
$\mathrm{dom}(A)$ is the set of variables $x$ for which $A$ contains $\{M/x\}$ not under a restriction on $x$. Processes are identified up to renaming of bound
names and variables. Substitutions are cycle-free, each variable has at most one active substitution, $\mathrm{dom}(A) \cap \mathrm{dom}(B) = \emptyset$ in every $A \mid B$,
and $x \in \mathrm{dom}(A)$ in every $\nu x.A$. $A$ is *closed* when $\mathrm{dom}(A) = \mathrm{fv}(A)$. A *frame* $\varphi$ is an extended process built from $0$ and active
substitutions by parallel composition and restriction, and the frame $\varphi(A)$ of $A$ replaces every plain process in $A$ by $0$. An *evaluation context* is
an extended process with a hole that is not under replication, a conditional, an input or an output.

## Depends on

- [Equational theories and convergent subterm theories](equational-theories-and-convergent-subterm-theories.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 2.1 (terms over infinitely many names and variables of each sort, the sort system of Figure 2 and the convention that expressions are well sorted and substitutions preserve sorts, plain and extended processes, Figure 1 for free names, free variables and domains, frames and the sort system) and Section 2.2 (evaluation contexts).
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 5.1 (syntax and informal semantics).
