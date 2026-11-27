# Synthesis problem for interval temporal logic with an equivalence over points

The synthesis problem for fragments of Halpern and Shoham's interval logic with an equivalence relation on points is a two-player game on the intervals of a linear order: one player labels each interval with the letters and temporal requests he controls, the other completes the labeling, and the second player's goal is that the resulting interval structure be a model of a given formula.

**Logic.** Let $\Sigma$ be a set of proposition letters containing a special letter $\sim$. Formulas of $\mathsf{A\bar{A}B\bar{B}}{\sim}$ are built from letters with $\neg$, $\vee$ and the unary modalities $\langle A\rangle$, $\langle \bar{A}\rangle$, $\langle B\rangle$, $\langle \bar{B}\rangle$; the fragments $\mathsf{A\bar{A}B\bar{B}}$, $\mathsf{AB\bar{B}}{\sim}$ and $\mathsf{AB\bar{B}}$ omit $\sim$, $\langle\bar{A}\rangle$, or both. Over a linear order $(D,<)$ the intervals are $[x,y]$ with $x \leq y$ (non-strict semantics), and an interval structure labels each interval with a set of letters. The relations are $[x,y]\,A\,[x',y'] \iff y = x'$ (meets), $\bar{A}$ its converse (met by), $[x,y]\,B\,[x',y'] \iff x = x' \wedge y' < y$ (begun by) and $\bar{B}$ its converse (begins); $\langle R \rangle\varphi$ is true at $I$ iff $\varphi$ is true at some $J$ with $I \mathrel{R} J$. The letter $\sim$ is interpreted by an equivalence relation on points: $[x,y]$ satisfies $\sim$ iff $x \sim y$.

**Synthesis.** Fix a formula $\varphi$ and a set $\Sigma^T_{\Box}$ of letters and temporal requests (subformulas $\langle R\rangle\psi$) controlled by the spoiler; the duplicator controls the others. The temporal domain is $\mathbb{N}$ or a finite prefix $\{0, \dots, m-1\}$. A play visits every interval exactly once, in an order in which all intervals ending at $y$ are visited before any interval ending at $y+1$; at each visited interval the spoiler first fixes the truth of his letters and requests there, then the duplicator fixes the rest. The play induces an interval structure, and it is *successful* if this structure satisfies $\varphi$ at $[0,0]$ and the guessed truth values of the requests and subformulas are correct. The pair $(\varphi, \Sigma^T_{\Box})$ admits a *finite synthesis* if the duplicator has a response strategy such that every play has a successful finite prefix covering all intervals over some $\{0,\dots,m-1\}$, and admits an *$\mathbb{N}$-synthesis* if she has one making every infinite play successful.

## Depends on

None.

## Proof depends on

None.

## Expansion

The problem is the interval analogue of Büchi and Landweber's synthesis problem for monadic second-order logic of one successor. Synthesis can force properties that satisfiability in the same fragment cannot express, for instance duration comparisons between consecutive events in $\mathsf{AB\bar{B}}$.

## Sources

- Angelo Montanari and Pietro Sala, "Interval-based synthesis", in *Proceedings Fifth International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2014)*, Electronic Proceedings in Theoretical Computer Science 161, 2014, pp. 102–115, doi:10.4204/EPTCS.161.11; read as arXiv:1408.5960v1, <https://arxiv.org/abs/1408.5960v1>: Section 2 (the logic $\mathsf{A\bar{A}B\bar{B}}{\sim}$ and its fragments) and Section 3 (admissible runs, response strategies and Definition 2 of finite synthesis, with its $\mathbb{N}$ variant) of arXiv:1408.5960v1.
