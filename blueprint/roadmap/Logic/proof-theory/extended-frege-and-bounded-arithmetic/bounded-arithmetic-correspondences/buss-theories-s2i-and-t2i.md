# Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$

Buss's theories $S^i_2$ and $T^i_2$ are fragments of arithmetic with induction restricted to $\Sigma^b_i$-formulas, polynomial induction for $S^i_2$ and ordinary induction for $T^i_2$. Their bounded formulas define exactly the levels of the polynomial hierarchy.

The language $L$ has the symbols $0$, $S$, $+$, $\cdot$, $|x|$, $\lfloor x/2\rfloor$, $\#$ and $\le$, where $|x|=\lceil\log_2(x+1)\rceil$ is the length of the binary representation of $x$ and $x\#y=2^{|x|\cdot|y|}$. A quantifier $(\forall x\le t)$ or $(\exists x\le t)$ with $t$ a term not containing $x$ is *bounded*, and *sharply bounded* if $t$ has the form $|s|$. The classes $\Sigma^b_i$ and $\Pi^b_i$ of bounded formulas are defined by counting alternations of bounded quantifiers in prenex form, ignoring sharply bounded quantifiers; $\Sigma^b_0=\Pi^b_0$ consists of the formulas with only sharply bounded quantifiers.

Let BASIC be Buss's finite set of open axioms fixing the meaning of the symbols. The induction schemes are

$$
\mathrm{IND}:\ \varphi(0)\wedge\forall x\,(\varphi(x)\to\varphi(x+1))\to\forall x\,\varphi(x), \qquad \mathrm{PIND}:\ \varphi(0)\wedge\forall x\,(\varphi(\lfloor x/2\rfloor)\to\varphi(x))\to\forall x\,\varphi(x),
$$

$$
\mathrm{LIND}:\ \varphi(0)\wedge\forall x\,(\varphi(x)\to\varphi(x+1))\to\forall x\,\varphi(|x|).
$$

For $i\ge 0$, $S^i_2$ is BASIC together with $\mathrm{PIND}$ for $\Sigma^b_i$-formulas, and $T^i_2$ is BASIC together with $\mathrm{IND}$ for $\Sigma^b_i$-formulas; $S_2=\bigcup_i S^i_2$ (PIND for all bounded formulas) and $T_2=\bigcup_i T^i_2$.

Facts recorded in the sources:

- In the standard model, $\Sigma^b_1$-formulas define exactly the NP subsets of $\mathbb N$ and $\Pi^b_1$-formulas the coNP subsets; more generally $\Sigma^b_i$ defines the sets in $\Sigma^p_i$ for $i\ge 1$.
- $S^1_2$ is equivalently axiomatized by BASIC with $\Sigma^b_1$-LIND, with $\Pi^b_1$-LIND, or with $\Pi^b_1$-PIND; for $i\ge1$, $S^i_2$ is axiomatized by $\Sigma^b_i$-LIND.
- $T^0_2\subseteq S^1_2\subseteq T^1_2\subseteq S^2_2\subseteq T^2_2\subseteq\cdots$.
- $S_2$ is finitely axiomatizable if and only if the polynomial hierarchy collapses and the collapse is provable in $S_2$ (Buss; Zambella). For $i\ge 1$, if $T^i_2=S^{i+1}_2$ then $\Sigma^p_{i+2}=\Pi^p_{i+2}$ (Krajíček, Pudlák and Takeuti). Pudlák states this for all $i\ge 0$ under the convention, described below, that enlarges $\Sigma^b_0$ to all polynomial-time sets; with the convention above the case $i=0$ concerns a weaker $T^0_2$, and Buss proves the collapse of the polynomial hierarchy for $i=0$ from $T^0_2(\mathrm{PV})=S^1_2$.

## Expansion

The smash function $\#$ gives terms polynomial growth in the lengths of their arguments, so bounded quantifiers range over strings of polynomial length, exactly what is needed to code polynomial-time computations. The index 2 refers to the presence of $\#$, and the superscript $i$ to the amount of induction. Polynomial induction runs over the length of numbers, which matches polynomial-time recursion on notation; $S^1_2$ is the theory whose provably total $\Sigma^b_1$-definable functions are the polynomial-time functions, and it corresponds to extended Frege. Pudlák works with a variant convention in which $\Sigma^b_0$ is enlarged to define all polynomial-time sets, which affects only $T^0_2$.

## Depends on

- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [The class $\Sigma_k^p$](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sigma-k.md)

## Proof depends on

None.

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 5: the language $L$, bounded and sharply bounded quantifiers, $\Sigma^b_i$ and $\Pi^b_i$, Theorem 5.1, the axiomatizations of $S^1_2$ and $S^i_2$; Section 1: finite axiomatizability of $S_2$; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Pavel Pudlák, "Some relations between subsystems of arithmetic and complexity of computations", in *Logic from Computer Science* (Y. N. Moschovakis, ed.), MSRI Publications 21, Springer, 1992, pp. 499–519, doi:10.1007/978-1-4612-2822-6_19 (Section 2: IND, PIND, LIND, the fragments $S^i_2$ and $T^i_2$, the chain of inclusions, and the convention on $\Sigma^b_0$, which "influences only the weakest fragment" $T^0_2$; Section 1: the collapse result of Krajíček, Pudlák and Takeuti).
- Pavel Pudlák, "Incompleteness in the finite domain", *Bulletin of Symbolic Logic* 23(4):405–441, 2017, doi:10.1017/bsl.2017.32, arXiv:1601.01487v2 (Section 2.2: the theories $S_2$ and $S^i_2$; Section 2.3: the classes $\Sigma^b_n$, $\Pi^b_n$).
- Samuel R. Buss, "Bounded arithmetic and propositional proof complexity", in *Logic of Computation* (H. Schwichtenberg, ed.), Springer, 1997, author's copy <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/paper.pdf> (Section 2: the theories $S^i_2$ and $T^i_2$; Theorem 3: $T^i_2\vdash S^i_2$ and $S^i_2\vdash T^{i-1}_2$ for $i\ge 1$; Section 4.4, Theorem 23 (Krajíček, Pudlák and Takeuti; Buss; Zambella): if $T^i_2=S^{i+1}_2$ the polynomial hierarchy collapses, with the case $i=0$ proved for $T^0_2(\mathrm{PV})$).
