# Buss's witnessing theorem

If $S^{i+1}_2$ proves $\forall x\,\exists y\,\varphi(x,y)$ for a $\Sigma^b_{i+1}$-formula $\varphi$, then a witness $y$ can be computed from $x$ in polynomial time with a $\Sigma^p_i$ oracle; for $i=0$, the provably total $\Sigma^b_1$-definable functions of $S^1_2$ are polynomial-time computable.

**Theorem (Buss).** Let $i\ge 0$, let $\varphi(x,y)$ be a $\Sigma^b_{i+1}$-formula, and suppose $S^{i+1}_2\vdash\forall x\,\exists y\,\varphi(x,y)$. Then there is a function $f$ computable in polynomial time with an oracle from $\Sigma^p_i$ such that $\mathbb N\vDash\forall x\,\varphi(x,f(x))$. Moreover $S^{i+1}_2\vdash\forall x\,\varphi(x,f(x))$ for a suitable definition of $f$.

**Case $i=0$.** If $\varphi(x,y)$ is $\Sigma^b_1$ and $S^1_2\vdash\forall x\,\exists y\,\varphi(x,y)$, then there is a polynomial-time computable function $f$ with $\mathbb N\vDash\forall x\,\varphi(x,f(x))$, and $f$ is definable by a $\Sigma^b_1$-formula: there is a $\Sigma^b_1$-formula $\psi(x,y)$ defining the graph of $f$ in $\mathbb N$ with $S^1_2\vdash\forall x\,\exists!y\,\psi(x,y)\wedge\forall x\,\forall y\,(\psi(x,y)\to\varphi(x,y))$.

## Expansion

By cut elimination a proof of $\forall x\,\exists y\,\varphi$ can be assumed free-cut free, so every formula in it is $\Sigma^b_{i+1}$ or $\Pi^b_{i+1}$. One then shows by induction on the proof that every sequent with $\Sigma^b_{i+1}$ succedent can be witnessed by a function in the class: logical rules compose witnesses, and an application of $\Sigma^b_{i+1}$-PIND, which runs over the $|x|$ bits of $x$, corresponds to polynomially many iterations of a witnessing function. The theorem is the model for many witnessing theorems characterizing the provably total functions of bounded arithmetic theories; for $T^i_2$ and $S^{i+1}_2$ with $\forall\exists\forall$ conclusions one obtains Krajíček–Pudlák–Takeuti style counterexample computations instead.

## Depends on

- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](buss-theories-s2i-and-t2i.md)
- [The class $\Sigma_k^p$](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sigma-k.md)
- [Polynomial time with an oracle](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

None.

## Sources

- Pavel Pudlák, "Some relations between subsystems of arithmetic and complexity of computations", in *Logic from Computer Science* (Y. N. Moschovakis, ed.), MSRI Publications 21, Springer, 1992, pp. 499–519, doi:10.1007/978-1-4612-2822-6_19 (Section 6, Theorem 1: Buss's theorem for $S^{i+1}_2$ and $\Sigma^b_{i+1}$-formulas with a $\Sigma^p_i$ oracle, including provability of $\forall x\,\varphi(x,f(x))$; Theorems 2 and 3 for counterexample computations).
- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 5, Theorem 5.2: the case $i=0$; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Pavel Pudlák, "Incompleteness in the finite domain", *Bulletin of Symbolic Logic* 23(4):405–441, 2017, doi:10.1017/bsl.2017.32, arXiv:1601.01487v2 (Section 2.3, Theorem 2.1, which assumes $S^1_2\vdash\forall x\,\exists y\,\varphi(x,y)$: the case $i=0$ with $f$ definable by a $\Sigma^b_1$-formula, and the meaning of that definability).
- Samuel R. Buss, "Bounded arithmetic and propositional proof complexity", in *Logic of Computation* (H. Schwichtenberg, ed.), Springer, 1997, author's copy <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/paper.pdf> (Section 2.6, Theorem 6 with $i=1$: the case $i=0$, with a $\Sigma^b_1$-formula $B$ such that $S^1_2\vdash\forall x\,\exists!y\,B(x,y)$ and $S^1_2\vdash B\to\varphi$; Corollary 9).
